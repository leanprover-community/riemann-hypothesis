import Development.WeilBound.ThetaLifts.FrameEstimates.WeilConv
import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
import Development.WeilBound.ThetaLifts.FrameEstimates.LatSumRedH
import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.LinDer
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf
import Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.WeilBound.ThetaLifts.FrameEstimates.IsCompactIntV
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_clm (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕)
    (hsb : φ ∈ SB _) (h : UA σ W.J) :
    ∃ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), L f = M.I om (pureA F f φ) h := by
  obtain ⟨h1, h2⟩ := dom_facts hB hp hD hφ hsb
  refine ⟨⟨⟨⟨fun f => M.I om (pureA F f φ) h, fun f f' => ?_⟩, fun c f => ?_⟩, h2 h⟩, fun _ => rfl⟩
  · have e : pureA F (f + f' : SInf F _) φ = pureA F f φ + pureA F f' φ := by
      funext x; simp [pureA, add_mul]
    unfold Model.I
    rw [e, ← integral_add ((h1 f).1 h) ((h1 f').1 h)]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_add hp (pureA_mem f hsb) (pureA_mem f' hsb) g h)
  · have e : pureA F (c • f : SInf F _) φ = c • pureA F f φ := by
      funext x; simp [pureA, mul_assoc]
    change M.I om (pureA F (c • f : SInf F _) φ) h = c * M.I om (pureA F f φ) h
    unfold Model.I
    rw [e, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_smul hp c (pureA_mem f hsb) g h)

theorem one_mem_UAt : (1 : UA σ X.J) ∈ UAt σ X (evI F) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem one_mem_Lines : (1 : Multiplicative ℝ →* UA σ X.J) ∈ Lines σ X := ⟨continuous_const, fun _ => one_mem_UAt⟩

end

theorem iDer_of (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) (hI : IInv) : IDer := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hD φ hφ hsb f hf
  obtain ⟨-, i2, i3⟩ := hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_UAt _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_Lines γ hγ T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have := hd L
    rw [hLf] at this
    convert this using 2 with t
    rw [hLf, ← (hT t).1.1 f φ hsb, i3]
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp _ (hγ.2 (Multiplicative.ofAdd t)) 1 one_mem_UAt
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ 1 one_mem_Lines T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, funext fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have h1 := hd L
    have h2 : (fun t => L (T t f)) = fun _ => M.I om (pureA F f φ) h := funext fun t => by
      rw [hLf, ← (hT t).1.1 f φ hsb, i2]
    rw [h2] at h1
    rw [← hLf]
    exact h1.unique (hasDerivAt_const _ _)

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem topGroup_UA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : IsTopologicalGroup (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin n) (AE F E)) := inferInstance
  exact Subgroup.instIsTopologicalGroupSubtypeMem _

theorem iInv_of_parts (hB : ThetaBasic) (hU : PositivityTheory.ThKF.Unimod) (hE : EpsOf) : IInv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ
  have hi := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1
  refine ⟨fun γ hγ h => ?_, fun g₀ => funext fun h => ?_, fun h h' => ?_⟩
  · simp only [Model.I]
    congr 1
    funext g
    simpa using hi 1 (one_mem _) γ hγ g h
  · obtain ⟨h1, -, h3⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j)
      (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1.2
    have := topGroup_UA σ X.J
    have := h3 _ hp.good.haar
    have := hp.good.haar
    have : BorelSpace (UA σ X.J) := ⟨rfl⟩
    have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
      simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [Model.I, e]
    exact PositivityTheory.ThKF.L2.integral_right hp.good.dom (fun g => theta om Φ g h)
      (fun γ hγ g => by simpa using hi γ hγ 1 (one_mem _) g h) g₀
  · simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem iInv_of (hB : ThetaBasic) : IInv := iInv_of_parts hB PositivityTheory.ThKF.unimodularity_holds epsOf_of

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem umgLin_pow_le {x C : ℝ} {z : ℂ} (hx : 1 ≤ x) {k m : ℕ} (hk : k ≤ m) (h : ‖z‖ ≤ C * x ^ k) :
    ‖z‖ ≤ |C| * x ^ m :=
  h.trans <| mul_le_mul (le_abs_self C) (pow_le_pow_right₀ hx hk) (pow_nonneg (zero_le_one.trans hx) k) (abs_nonneg C)

theorem umgLin_of : UMGLin := by
  intro F E _ _ _ _ _ σ _ _ d W _ f f' hf hf' a b
  obtain ⟨k, S, hfS, hS⟩ := hf
  obtain ⟨k', S', hfS', hS'⟩ := hf'
  refine ⟨max k k', {g | ∃ f₁ ∈ S, ∃ f₁' ∈ S', g = a • f₁ + b • f₁'}, ⟨f, hfS, f', hfS', rfl⟩, ?_⟩
  rintro _ ⟨g, hg, g', hg', rfl⟩
  obtain ⟨hc, ⟨C, hC⟩, hd⟩ := hS g hg
  obtain ⟨hc', ⟨C', hC'⟩, hd'⟩ := hS' g' hg'
  refine ⟨(hc.const_smul a).add (hc'.const_smul b), ⟨‖a‖ * |C| + ‖b‖ * |C'|, fun h => ?_⟩, fun γ hγ => ?_⟩
  · have hx : (1 : ℝ) ≤ (ht h : ℝ) := by exact_mod_cast one_le_ht h
    have h1 := umgLin_pow_le hx (le_max_left k k') (hC h)
    have h2 := umgLin_pow_le hx (le_max_right k k') (hC' h)
    have h3 : ‖(a • g + b • g') h‖ ≤ ‖a‖ * ‖g h‖ + ‖b‖ * ‖g' h‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h4 := mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
    have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg b)
    linarith
  · obtain ⟨g₂, hg₂, e⟩ := hd γ hγ
    obtain ⟨g₂', hg₂', e'⟩ := hd' γ hγ
    exact ⟨a • g₂ + b • g₂', ⟨g₂, hg₂, g₂', hg₂', rfl⟩, fun h => ((e h).const_mul a).add ((e' h).const_mul b)⟩

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst.UMGS

open Filter Topology Function

theorem hasFDerivAt_of_partials {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    ∀ (Φ : (Fin k → ℝ) → V) (D : Fin k → (Fin k → ℝ) → V), (∀ i, Continuous (D i)) →
      (∀ i t, HasDerivAt (fun s => Φ (update t i (t i + s))) (D i t) 0) →
      ∀ t, HasFDerivAt Φ (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i t)) t := by
  induction k with
  | zero =>
    intro Φ D _ _ t
    simpa using hasFDerivAt_of_subsingleton (𝕜 := ℝ) Φ t
  | succ k ih =>
    intro Φ D hc hd t
    have hcons : Continuous fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp continuous_snd
    have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (t 0, Fin.tail t))
      (f := fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u))
      (f₁ := fun s u => (ContinuousLinearMap.id ℝ ℝ).smulRight (D 0 (Fin.cons s u)))
      (f₂ := fun s u => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i.succ (Fin.cons s u)))
      (Eventually.of_forall fun v => by
        have h := hd 0 (Fin.cons v.1 v.2)
        simp only [Fin.update_cons_zero, Fin.cons_zero] at h
        have h0 : HasDerivAt (fun s => Φ (Fin.cons (v.1 + s) v.2)) (D 0 (Fin.cons v.1 v.2)) (v.1 - v.1) := by
          simpa using h
        have h1 := h0.comp_sub_const v.1 v.1
        simp only [add_sub_cancel] at h1
        exact h1.hasFDerivAt)
      (Eventually.of_forall fun v => ih (fun u => Φ (Fin.cons v.1 u)) (fun i u => D i.succ (Fin.cons v.1 u))
        (fun i => (hc i.succ).comp (hcons.comp (continuous_const.prodMk continuous_id)))
        (fun i u => by
          have h := hd i.succ (Fin.cons v.1 u)
          simpa only [Fin.cons_update, Fin.cons_succ] using h) v.2)
      (((ContinuousLinearMap.smulRightL ℝ ℝ V (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
        ((hc 0).comp hcons)).continuousAt)
      ((continuous_finsetSum Finset.univ fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) V (ContinuousLinearMap.proj i)).continuous.comp
          ((hc i.succ).comp hcons)).continuousAt)
    let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.succ i))
    have h2 := HasFDerivAt.comp (f := e) t key.hasFDerivAt e.hasFDerivAt
    have h3 : (↿fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u)) ∘ e = Φ := by
      funext x
      exact congrArg Φ (Fin.cons_self_tail x)
    rw [h3] at h2
    refine h2.congr_fderiv ?_
    ext1 x
    simp [e, HasUncurry.uncurry, Fin.sum_univ_succ, Fin.cons_self_tail]

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]

def pr {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (t : Fin k → ℝ) : G :=
  (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_succ {k : ℕ} (γ : Fin (k + 1) → (Multiplicative ℝ →* G)) (t : Fin (k + 1) → ℝ) :
    pr γ t = γ 0 (Multiplicative.ofAdd (t 0)) * pr (fun i => γ i.succ) (fun i => t i.succ) := by
  simp [pr, List.ofFn_succ]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_zero (γ : Fin 0 → (Multiplicative ℝ →* G)) (t : Fin 0 → ℝ) : pr γ t = 1 := by
  simp [pr]

def Gn (m : ι → G →* A) (γ : Multiplicative ℝ →* G) (Y : ι → A) : Prop :=
  ∀ w (t : ℝ), m w (γ (Multiplicative.ofAdd t)) = NormedSpace.exp (t • Y w)

theorem continuous_pr (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, Continuous (γ i)) → Continuous (pr γ) := by
  induction k with
  | zero => intro γ _; exact continuous_const.congr fun t => (pr_zero γ t).symm
  | succ k ih =>
    intro γ hγ
    refine Continuous.congr ?_ fun t => (pr_succ γ t).symm
    exact ((hγ 0).comp (continuous_ofAdd.comp (continuous_apply 0))).mul
      ((ih _ fun i => hγ i.succ).comp (continuous_pi fun i => continuous_apply _))

theorem contDiff_exp_smul (Y : A) (n : WithTop ℕ∞) : ContDiff ℝ n fun t : ℝ => NormedSpace.exp (t • Y) := by
  have h : ContDiff ℝ n (NormedSpace.exp : A → A) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact h.comp (contDiff_id.smul contDiff_const)

theorem contDiff_tail (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n fun (t : Fin (k + 1) → ℝ) (i : Fin k) => t i.succ :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem contDiff_pr (m : ι → G →* A) (n : WithTop ℕ∞) (w : ι) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G),
    (∀ i, ∃ Y, Gn m (γ i) Y) → ContDiff ℝ n (fun t => m w (pr γ t)) ∧ ContDiff ℝ n (fun t => m w (pr γ t)⁻¹) := by
  induction k with
  | zero => intro γ _; simp only [pr_zero]; exact ⟨contDiff_const, contDiff_const⟩
  | succ k ih =>
    intro γ hγ
    obtain ⟨h1, h2⟩ := ih (fun i => γ i.succ) fun i => hγ i.succ
    obtain ⟨Y, hY⟩ := hγ 0
    simp only [pr_succ, mul_inv_rev, map_mul, ← map_inv, ← ofAdd_neg, hY w]
    exact ⟨((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ ℝ 0)).mul (h1.comp (contDiff_tail k n)),
      (h2.comp (contDiff_tail k n)).mul ((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ ℝ 0).neg)⟩

def cj (x : G) (γ : Multiplicative ℝ →* G) : Multiplicative ℝ →* G := (MulAut.conj x⁻¹).toMonoidHom.comp γ

omit [TopologicalSpace G] [ContinuousMul G] in
theorem cj_apply (x : G) (γ : Multiplicative ℝ →* G) (s : Multiplicative ℝ) : cj x γ s = x⁻¹ * γ s * x := by
  simp [cj]

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem Gn.cj {m : ι → G →* A} {γ : Multiplicative ℝ →* G} {Y : ι → A} (h : Gn m γ Y) (x : G) :
    Gn m (cj x γ) fun w => m w x⁻¹ * Y w * m w x := by
  intro w t
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let u : Aˣ := Units.map (m w) (toUnits x⁻¹)
  have h1 : (u : A) = m w x⁻¹ := rfl
  have h2 : ((u⁻¹ : Aˣ) : A) = m w x := by simp [u]
  have := NormedSpace.exp_units_conj u (t • Y w)
  rw [h1, h2] at this
  rw [cj_apply, map_mul, map_mul, h w t, ← this, mul_smul_comm, smul_mul_assoc]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem exists_partial (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G)) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L)
    (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y) (n : WithTop ℕ∞) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, γ i ∈ L) →
    ∀ i, ∃ Z : (Fin k → ℝ) → ι → A, ContDiff ℝ n Z ∧ ∀ t, ∃ γ' ∈ L, Gn m γ' (Z t) ∧
      ∀ s, pr γ (update t i (t i + s)) = pr γ t * γ' (Multiplicative.ofAdd s) := by
  induction k with
  | zero => intro γ _ i; exact i.elim0
  | succ k ih =>
    intro γ hγ i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨Y, hY⟩ := hg _ (hγ 0)
      refine ⟨fun t w => m w (pr (fun i => γ i.succ) fun i => t i.succ)⁻¹ * Y w *
        m w (pr (fun i => γ i.succ) fun i => t i.succ), contDiff_pi.2 fun w => ?_, fun t =>
        ⟨_, hcj _ (hγ 0) _, hY.cj _, fun s => ?_⟩⟩
      · obtain ⟨h1, h2⟩ := contDiff_pr m n w k (fun i => γ i.succ) fun i => hg _ (hγ i.succ)
        exact ((h2.comp (contDiff_tail k n)).mul contDiff_const).mul (h1.comp (contDiff_tail k n))
      · simp only [pr_succ, cj_apply, update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true, update_of_ne,
          ofAdd_add, map_mul]
        group
    · obtain ⟨Z, hZ, h⟩ := ih (fun i => γ i.succ) (fun i => hγ i.succ) j
      refine ⟨fun t => Z fun i => t i.succ, hZ.comp (contDiff_tail k n), fun t => ?_⟩
      obtain ⟨γ', h1, h2, h3⟩ := h fun i => t i.succ
      refine ⟨γ', h1, h2, fun s => ?_⟩
      have e : (fun i : Fin k => update t j.succ (t j.succ + s) i.succ) =
          update (fun i : Fin k => t i.succ) j (t j.succ + s) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [hi]
      rw [pr_succ, pr_succ, e, h3, update_of_ne (Fin.succ_ne_zero j).symm, mul_assoc]

theorem contDiff_comp_pr [FiniteDimensional ℝ A] (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G))
    (hc : ∀ γ ∈ L, Continuous γ) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L) (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y)
    {r : ℕ} (β : Fin r → (Multiplicative ℝ →* G)) (c : Fin r → (ι → A) →ₗ[ℝ] ℝ) (hβ : ∀ j, β j ∈ L)
    (hl : ∀ (f : G → ℂ) (f' : Fin r → G → ℂ), (∀ j, Continuous (f' j) ∧
      ∀ h, HasDerivAt (fun t : ℝ => f (h * β j (Multiplicative.ofAdd t))) (f' j h) 0) → ∀ γ ∈ L, ∀ Y, Gn m γ Y →
      ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ j, (c j Y : ℂ) * f' j h) 0)
    (S : Set (G → ℂ)) (hS : ∀ f ∈ S, Continuous f ∧
      ∀ γ ∈ L, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0)
    {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (hγ : ∀ i, γ i ∈ L) (g : G) (n : ℕ) :
    ∀ f ∈ S, ContDiff ℝ n fun t => f (g * pr γ t) := by
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.2 ((hS f hf).1.comp (continuous_const.mul (continuous_pr k γ fun i => hc _ (hγ i))))
  | succ n ih =>
    intro f hf
    choose f' hf'S hf' using fun j => (hS f hf).2 _ (hβ j)
    choose Z hZ hZ' using exists_partial m L hcj hg n k γ hγ
    have hD : ∀ i, ContDiff ℝ n fun t => ∑ j, (c j (Z i t) : ℂ) * f' j (g * pr γ t) := fun i =>
      ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp
        ((LinearMap.toContinuousLinearMap (c j)).contDiff.comp (hZ i))).mul (ih _ (hf'S j))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, hasFDerivAt_of_partials k _ _ (fun i => (hD i).continuous) fun i t => ?_⟩
    · exact ContDiff.sum fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hD i)
    · obtain ⟨γ', h1, h2, h3⟩ := hZ' i t
      simp only [h3, ← mul_assoc]
      exact hl f f' (fun j => ⟨(hS _ (hf'S j)).1, hf' j⟩) γ' h1 _ h2 _

end PositivityTheory.ThKEst.UMGS

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def umgComp (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (w : InfinitePlace F) :
    UA σ J →* Matrix (Fin d) (Fin d) ℂ :=
  (piInf (τ w)).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

theorem umg_continuousMul {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : ContinuousMul (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  exact (Subgroup.instIsTopologicalGroupSubtypeMem _).toContinuousMul

theorem umg_cj_mem {d : ℕ} {W : Spc F E d} {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) (x : UA σ W.J) :
    UMGS.cj x γ ∈ Lines σ W := by
  have := umg_continuousMul (σ := σ) W.J
  refine ⟨((continuous_const.mul hγ.1).mul continuous_const).congr fun s => (UMGS.cj_apply x γ s).symm,
    fun t u hu => ?_⟩
  have h := hγ.2 t u hu
  have hm : ∀ a b : UA σ W.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have h1 : mat x⁻¹ * mat x = 1 := by rw [← hm, inv_mul_cancel]; rfl
  have e : mat (UMGS.cj x γ t) - 1 = mat x⁻¹ * (mat (γ t) - 1) * mat x := by
    rw [UMGS.cj_apply, hm, hm, mul_sub, sub_mul, mul_one, h1]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero, Matrix.zero_mul]

open scoped Matrix.Norms.Operator in
theorem umgSmooth_of (hL : LinDer) (hG : LineGen) : UMGSmooth := by
  intro F E _ _ _ _ _ σ hcm τ d W hW f hf k γ hγ g
  obtain ⟨r, β, c, hβ, hl⟩ := hL F E σ hcm τ d W hW
  obtain ⟨k₀, S, hfS, hS⟩ := hf
  have := umg_continuousMul (σ := σ) W.J
  have hGn : ∀ (δ : Multiplicative ℝ →* UA σ W.J) Y, UMGS.Gn (umgComp τ W.J) δ Y ↔ Gen τ W δ Y := fun δ Y =>
    forall₂_congr fun w t => by rw [Complex.coe_smul]; rfl
  refine contDiff_infty.2 fun n => ?_
  exact UMGS.contDiff_comp_pr (umgComp τ W.J) (Lines σ W) (fun _ h => h.1) (fun _ h x => umg_cj_mem h x)
    (fun δ h => (hG F E σ hcm τ d W hW δ h).imp fun Y hY => (hGn δ Y).2 hY.2) β c hβ
    (fun f f' h δ hδ Y hY => hl f f' h δ hδ Y ((hGn δ Y).1 hY)) S
    (fun f hf => ⟨(hS f hf).1, (hS f hf).2.2⟩) γ hγ g n f hfS

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineGeneration

set_option linter.unusedSectionVars false

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_deriv {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, ∀ t, HasDerivAt g (g t * Y) t := by
  let G : ℝ → A := fun t => ∫ s in (0 : ℝ)..t, g s
  have hG : ∀ t, HasDerivAt G (g t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have h1 : Tendsto (slope G 0) (𝓝[≠] 0) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hG 0)
    rwa [h0] at this
  have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), IsUnit (slope G 0 h) := h1 (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hu, hne⟩ := (h2.and self_mem_nhdsWithin).exists
  have hne' : h ≠ 0 := hne
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  rw [slope_def_module, hG0, sub_zero, sub_zero] at hv
  have hv' : G h * (h⁻¹ • v) = 1 := by rw [mul_smul_comm, ← smul_mul_assoc, hv]
  set u := h⁻¹ • v
  have key : ∀ t, g t * G h = G (t + h) - G t := by
    intro t
    have e1 : g t * G h = ∫ s in (0 : ℝ)..h, g (t + s) := by
      simp only [ha]
      exact ((ContinuousLinearMap.mul ℝ A (g t)).intervalIntegral_comp_comm (hc.intervalIntegrable 0 h)).symm
    rw [e1, intervalIntegral.integral_comp_add_left, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have e : g = fun t => (G (t + h) - G t) * u := by
    funext t
    rw [← key, mul_assoc, hv', mul_one]
  refine ⟨(g h - 1) * u, fun t => ?_⟩
  have d := (((hG (t + h)).comp_add_const t h).sub (hG t)).mul_const u
  have e2 : g t * ((g h - 1) * u) = (g (t + h) - g t) * u := by
    rw [← mul_assoc, mul_sub, mul_one, ha]
  rw [e2]
  exact d.congr_of_eventuallyEq (Eventually.of_forall fun s => congrFun e s)

theorem exists_exp {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, HasDerivAt g Y 0 ∧ ∀ t, g t = NormedSpace.exp (t • Y) := by
  obtain ⟨Y, hY⟩ := exists_deriv hc h0 ha
  refine ⟨Y, by simpa [h0] using hY 0, fun t => ?_⟩
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g s * NormedSpace.exp ((t - s) • Y)) 0 s := by
    intro s
    have d1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
    have d2 := (hY s).mul d1
    refine d2.congr_deriv ?_
    simp [mul_assoc]
  have c := is_const_of_deriv_eq_zero (fun s => (d s).differentiableAt) (fun s => (d s).deriv) t 0
  simpa [h0] using c

end Banach

set_option backward.isDefEq.respectTransparency false in
theorem mat_exp {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} (hc : Continuous g) (h0 : g 0 = 1)
    (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, (∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) ∧
      ∀ t : ℝ, g t = NormedSpace.exp ((t : ℂ) • Y) := by
  open scoped Matrix.Norms.Operator in
  obtain ⟨Y, h1, h2⟩ := exists_exp (A := Matrix (Fin d) (Fin d) ℂ) hc h0 ha
  refine ⟨Y, fun i j => ?_, fun t => ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
      Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  · rw [h2 t, Complex.coe_smul]

theorem lie_of_unitary {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} {J Y : Matrix (Fin d) (Fin d) ℂ} (h0 : g 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) (hu : ∀ t, (g t)ᵀ * J * (g t).map star = J) :
    Yᵀ * J + J * Y.map star = 0 := by
  ext i j
  have d1 : HasDerivAt (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j))
      (∑ l, ((∑ k, Y k i * J k l) * star (g 0 l j) + (∑ k, g 0 k i * J k l) * star (Y l j))) 0 :=
    HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun k _ => (hd k i).mul_const (J k l)).fun_mul (hd l j).star
  have e : (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j)) = fun _ => J i j := by
    funext t
    rw [← congrFun (congrFun (hu t) i) j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [e] at d1
  have z := d1.unique (hasDerivAt_const (0 : ℝ) (J i j))
  have e1 : (Yᵀ * J * (g 0).map star + (g 0)ᵀ * J * Y.map star) i j = 0 := by
    rw [← z, Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rwa [h0, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul] at e1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul' {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : E) :
    piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x := by
  change infEmb τ (evInf F w a ⊗ₜ[F] x) = _
  rw [infEmb_tmul]
  rfl

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change piInf τ (a ⊗ₜ[F] (1 : E)) = _
    rw [piInf_tmul', map_one, mul_one]
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hw : w.IsReal := h.1.isReal w
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul', piInf_tmul', h.2.2.2, star_mul',
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [Complex.star_def, Complex.conj_ofReal]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul' τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

end ExponentialLineGeneration

open ExponentialLineGeneration in
theorem lineGen_of : LineGen := by
  intro F E _ _ _ _ _ σ h τ d W _ γ hγ
  have main : ∀ w, ∃ Y : Matrix (Fin d) (Fin d) ℂ,
      Yᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * Y.map star = 0 ∧
      ∀ t : ℝ, (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y) := by
    intro w
    let g : ℝ → Matrix (Fin d) (Fin d) ℂ := fun t => (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w))
    have hm : Continuous (mat : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hc : Continuous g :=
      ((hm.comp (hγ.1.comp continuous_ofAdd))).matrix_map (continuous_piInf (τ w))
    have h0 : g 0 = 1 := by
      change (mat (γ 1)).map (piInf (τ w)) = 1
      rw [map_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have ha : ∀ s t, g (s + t) = g s * g t := by
      intro s t
      change (mat (γ (Multiplicative.ofAdd s * Multiplicative.ofAdd t))).map (piInf (τ w)) = _
      rw [map_mul]
      exact Matrix.map_mul
    obtain ⟨Y, h1, h2⟩ := mat_exp hc h0 ha
    refine ⟨Y, lie_of_unitary h0 h1 fun t => ?_, h2⟩
    have hu : (mat (γ (Multiplicative.ofAdd t)))ᵀ * incM F W.J * (mat (γ (Multiplicative.ofAdd t))).map (cA σ) =
        incM F W.J := (γ (Multiplicative.ofAdd t)).2
    have e : ((mat (γ (Multiplicative.ofAdd t))).map (cA σ)).map (piInf (τ w)) = (g t).map star := by
      ext i j
      exact piInf_cA h _ _
    have hv := congrArg (fun M : Matrix (Fin d) (Fin d) (AE F E) => M.map (piInf (τ w))) hu
    simp only [Matrix.map_mul] at hv
    rwa [Matrix.transpose_map, map_incM, e] at hv
  choose Y hY using main
  exact ⟨Y, fun w => (hY w).1, fun w => (hY w).2⟩

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineExistence

open GlobalTheory.CompanionTheory.CMAdele

section Cx

variable {d : ℕ}

theorem exp_line_add (Y : Matrix (Fin d) (Fin d) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _), Complex.ofReal_add, add_smul]

theorem exp_map_star (A : Matrix (Fin d) (Fin d) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have e : ∀ B : Matrix (Fin d) (Fin d) ℂ, B.map star = Bᴴᵀ := fun B => rfl
  rw [e, e, Matrix.exp_transpose, Matrix.exp_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
theorem exp_semiconj {J A B : Matrix (Fin d) (Fin d) ℂ} (h : SemiconjBy J A B) :
    NormedSpace.exp (-B) * J * NormedSpace.exp A = J :=
  open scoped Matrix.Norms.Operator in h.exp_neg_mul_mul_exp_eq_self

set_option backward.isDefEq.respectTransparency false in
theorem continuous_exp_mat : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
  open scoped Matrix.Norms.Operator in NormedSpace.exp_continuous

theorem exp_unitary {J Y : Matrix (Fin d) (Fin d) ℂ} (h : Yᵀ * J + J * Y.map star = 0) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᵀ * J * (NormedSpace.exp ((t : ℂ) • Y)).map star = J := by
  have h1 : SemiconjBy J (((t : ℂ) • Y).map star) (-((t : ℂ) • Y)ᵀ) := by
    have e : ((t : ℂ) • Y).map star = (t : ℂ) • Y.map star := by
      ext i j
      simp
    rw [SemiconjBy, e, Matrix.transpose_smul, Matrix.mul_smul, neg_mul, Matrix.smul_mul, ← smul_neg,
      eq_neg_of_add_eq_zero_right h]
  have h2 := exp_semiconj h1
  rwa [neg_neg, Matrix.exp_transpose, ← exp_map_star] at h2

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

theorem continuous_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (f := fun t => (realAd F t).1) (g := fun _ => (0 : Af F)) ?_ continuous_const
  refine continuous_pi fun w => ?_
  refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.isInducing.continuous_iff.2 ?_
  have e : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (realAd F t).1 w) = fun t : ℝ => (t : ℂ) :=
    funext fun t => GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd w t
  exact e ▸ Complex.continuous_ofReal

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ (∀ z, At (evI F) (s z)) ∧ ∀ z w, piInf (τ w) (s z) = z w := by
  classical
  choose x hx hx' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w 1)
  choose y hy hy' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w Complex.I)
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x w + realAd F (z w).im • y w), ?_, fun z c hc => ?_, fun z w => ?_⟩
  · have hr : ∀ (a : AE F E) (f : (InfinitePlace F → ℂ) → ℝ), Continuous f → Continuous fun z => realAd F (f z) • a :=
      fun a f hf => ((continuous_realAd (F := F)).comp hf).smul (continuous_const (y := a))
    refine continuous_finsetSum _ fun w _ => Continuous.add (hr _ _ ?_) (hr _ _ ?_)
    · exact Complex.continuous_re.comp (continuous_apply (A := fun _ => ℂ) w)
    · exact Complex.continuous_im.comp (continuous_apply (A := fun _ => ℂ) w)
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_comm c, smul_comm c, hx w c hc, hy w c hc, smul_zero, smul_zero, add_zero]
  · rw [map_sum, Finset.sum_eq_single w]
    · rw [map_add, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_same, Pi.single_eq_same, mul_one, Complex.re_add_im]
    · intro v _ hv
      rw [map_add, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, mul_zero, mul_zero, add_zero]
    · simp

variable {d : ℕ}

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u v : Matrix (Fin d) (Fin d) (AE F E)}
    (hf : ∀ c : AF F, evI F c = 0 → c • u = c • v) (e : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · rw [smul_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (hf c hc) i) j)
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

omit [NumberField E] in
theorem at_iff {u : Matrix (Fin d) (Fin d) (AE F E)} :
    At (evI F) (u - 1) ↔ ∀ c : AF F, evI F c = 0 → c • u = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) :=
  forall_congr' fun c => forall_congr' fun _ => by rw [smul_sub, sub_eq_zero]

theorem exists_matSection (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) :
    ∃ S : (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) → Matrix (Fin d) (Fin d) (AE F E), Continuous S ∧
      (∀ z (c : AF F), evI F c = 0 → c • S z = c • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      ∀ z w, (S z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hA, hp⟩ := exists_section h τ
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => Matrix.of fun i j => (1 : Matrix (Fin d) (Fin d) (AE F E)) i j +
    s fun w => z w i j - (1 : Matrix (Fin d) (Fin d) ℂ) i j, ?_, fun z c hc => ?_, fun z w => ?_⟩
  · refine continuous_matrix fun i j => continuous_const.add (hs.comp (continuous_pi fun w => ?_))
    exact ((continuous_apply w).matrix_elem i j).sub continuous_const
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply]
    rw [smul_add, hA _ c hc, add_zero]
  · ext i j
    have e := congrFun (congrFun (Matrix.map_one (n := Fin d) (piInf (τ w)) (map_zero _) (map_one _)) i) j
    rw [Matrix.map_apply] at e
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [map_add, hp, e, add_sub_cancel]

end ExponentialLineExistence

open ExponentialLineExistence in
theorem lineEx_of : LineEx := by
  intro F E _ _ _ _ _ σ h τ d W _ Y hY
  obtain ⟨S, hS, hf, hp⟩ := exists_matSection h τ d
  let g : ℝ → Matrix (Fin d) (Fin d) (AE F E) := fun t => S fun w => NormedSpace.exp ((t : ℂ) • Y w)
  have gp : ∀ t w, (g t).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w) := fun t w => hp _ w
  have gf : ∀ t (c : AF F), evI F c = 0 → c • g t = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) := fun t => hf _
  have gc : Continuous g := hS.comp (continuous_pi fun w =>
    continuous_exp_mat.comp (Complex.continuous_ofReal.smul continuous_const))
  have g0 : g 0 = 1 := mat_ext h τ (gf 0) fun w => by
    rw [gp, Matrix.map_one _ (map_zero _) (map_one _), Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  have ga : ∀ s t, g (s + t) = g s * g t := fun s t => mat_ext h τ
    (fun c hc => by rw [gf _ c hc, ← Matrix.smul_mul, gf _ c hc, Matrix.smul_mul, Matrix.one_mul, gf _ c hc])
    fun w => by rw [Matrix.map_mul, gp, gp, gp, exp_line_add]
  have gu : ∀ t, (g t)ᵀ * incM F W.J * (g t).map (cA σ) = incM F W.J := fun t => mat_ext h τ
    (fun c hc => by
      have e : ∀ u : Matrix (Fin d) (Fin d) (AE F E), c • u.map (cA σ) = (c • u).map (cA σ) := fun u => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, map_smul]
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, gf _ c hc, Matrix.transpose_smul,
        Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, e, gf _ c hc, ← e,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_smul, Matrix.mul_one])
    fun w => by
      have e : ((g t).map (cA σ)).map (piInf (τ w)) = ((g t).map (piInf (τ w))).map star := by
        ext i j
        exact piInf_cA h _ _
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_incM, e, gp]
      exact exp_unitary (hY w) t
  let G : ℝ → GL (Fin d) (AE F E) := fun t =>
    ⟨g t, g (-t), by rw [← ga, add_neg_cancel, g0], by rw [← ga, neg_add_cancel, g0]⟩
  let γ : Multiplicative ℝ →* UA σ W.J :=
    { toFun := fun t => ⟨G t.toAdd, gu _⟩
      map_one' := Subtype.ext (Units.ext g0)
      map_mul' := fun s t => Subtype.ext (Units.ext (ga _ _)) }
  refine ⟨γ, ⟨?_, fun t => at_iff.2 (gf _)⟩, fun w t => gp t w, fun γ' hγ' hG => ?_⟩
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact gc.comp continuous_toAdd
    · exact (gc.comp continuous_neg).comp continuous_toAdd
  · refine MonoidHom.ext fun t => Subtype.ext (Units.ext ?_)
    refine mat_ext h τ (u := mat (γ' t)) (v := g t.toAdd) (fun c hc => ?_) fun w => ?_
    · rw [at_iff.1 (hγ'.2 t) c hc, gf _ c hc]
    · rw [gp]
      exact hG w t.toAdd

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

namespace CuspR

open LatticeQuotientMeasure

def rat (H : Subgroup (GL (Fin n) (AE F E))) : Subgroup H :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf H

theorem ratPts_eq : ratPts σ J = rat (HR (AF F) σ J) := by
  have : Nontrivial (AE F E) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    exact ((infEmb τ).comp (compInf F E w)).domain_nontrivial
  ext g
  refine ⟨fun ⟨δ, _, hδ⟩ => ⟨δ, hδ⟩, fun ⟨δ, hδ⟩ => ⟨δ, ?_, hδ⟩⟩
  show cT (σ : E →+* E) δ.1 * J * δ.1 = J
  apply Matrix.map_injective (inclR (F := F) (E := E) (AF F)).injective
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have e : δ.1.map (inclR (F := F) (AF F)) = (matHom _ σ J g).1 := congrArg Units.val hδ
  rw [← e] at hg
  simp only [Matrix.map_mul]
  exact hg

theorem exists_herm (h : IsCMExt F E σ) (hJ : EpsHerm σ J) : ∃ c : E, c ≠ 0 ∧ IsHermND σ (c • J.map σ) := by
  have hσ := sigma_sigma h
  have hd : ∀ c : E, c ≠ 0 → (c • J.map σ).det ≠ 0 := fun c hc => by
    have e : (J.map σ).det = σ J.det := ((σ : E →+* E).map_det _).symm
    rw [det_smul, e]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero σ).2 hJ.2)
  rcases hJ.1 with h1 | h1
  · exact ⟨1, one_ne_zero, fun i j => by simp [h1], hd 1 one_ne_zero⟩
  · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra! hx
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have := h.2.1
      refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
      rw [ComplexEmbedding.isReal_iff]
      ext z
      have := h.2.2.2 τ z
      rw [hx] at this
      exact this.symm
    refine ⟨σ x - x, sub_ne_zero.2 hx, fun i j => ?_, hd _ (sub_ne_zero.2 hx)⟩
    simp only [Matrix.smul_apply, map_apply, smul_eq_mul, map_mul, map_sub, hσ, h1 j i]
    ring

omit [NumberField F] [NumberField E] in
theorem gram (hσ : ∀ x, σ (σ x) = x) (c : E) (Z : Matrix (Fin n) (Fin r) E) (u : Fin n → E) (i : Fin r) :
    ((cT (σ : E →+* E) Z * (c • J.map σ)) *ᵥ u) i = c * σ (form σ J (fun k => Z k i) u) := by
  simp only [form, mulVec, dotProduct, Matrix.mul_apply, cT, transpose_apply, map_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, hσ, RingHom.coe_coe, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem swap (hσ : ∀ x, σ (σ x) = x) (hJ : EpsHerm σ J) {x y : Fin n → E} (e : form σ J x y = 0) :
    form σ J y x = 0 := by
  have e2 := congrArg σ e
  simp only [form, mulVec, dotProduct, map_sum, map_mul, hσ, map_zero, Finset.mul_sum] at e2 ⊢
  rw [Finset.sum_comm]
  rcases hJ.1 with h1 | h1
  · rw [← e2]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [h1]; ring
  · rw [← neg_zero, ← e2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [h1]; ring

omit [NumberField F] [NumberField E] in
theorem perp_span {S : Set (Fin n → E)} {z : Fin n → E} (h : ∀ u ∈ S, form σ J u z = 0) :
    ∀ u ∈ Submodule.span E S, form σ J u z = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact zero_dotProduct _
  | add x y _ _ hx hy => rw [form, add_dotProduct]; exact (congrArg₂ (· + ·) hx hy).trans (add_zero 0)
  | smul a x _ hx => rw [form, smul_dotProduct]; exact (congrArg (a • ·) hx).trans (smul_zero a)

omit [NumberField F] [NumberField E] in
theorem perp_iff (hσ : ∀ x, σ (σ x) = x) (hJ : EpsHerm σ J) {c : E} (hc : c ≠ 0) (C : Matrix (Fin n) (Fin r) E)
    (z : Fin n → E) : (∀ u ∈ Submodule.span E (Set.range Cᵀ), form σ J z u = 0) ↔
      (cT (σ : E →+* E) C * (c • J.map σ)) *ᵥ z = 0 := by
  constructor
  · intro h
    funext i
    have e : form σ J (fun k => C k i) z = 0 := swap hσ hJ (h (Cᵀ i) (Submodule.subset_span ⟨i, rfl⟩))
    rw [gram hσ, e, map_zero, mul_zero]; rfl
  · intro h u hu
    refine swap hσ hJ (perp_span ?_ u hu)
    rintro _ ⟨i, rfl⟩
    have := (gram (J := J) hσ c C z i).symm.trans (congrFun h i)
    have e : form σ J (fun k => C k i) z = 0 := by simpa [hc] using this
    exact e

def unip (H : Subgroup (GL (Fin n) (AE F E))) (U : Submodule E (Fin n → E)) (P : (Fin n → E) → Prop) : Subgroup H :=
  Subgroup.closure {m | (∀ u ∈ U, m.1.1 *ᵥ incV F u = incV F u) ∧ ∀ z : Fin n → E, P z →
    m.1.1 *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (U : Set (Fin n → E)))}

def Van {H : Subgroup (GL (Fin n) (AE F E))} (Γ N : Subgroup H) (f : H → ℂ) : Prop :=
  letI : MeasurableSpace H := borel H
  ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ →
    ∀ h, ∫ u in 𝓕, f (u.1 * h) ∂μ = 0

def lines (H : Subgroup (GL (Fin n) (AE F E))) : Set (Multiplicative ℝ →* H) :=
  {γ | Continuous γ ∧ ∀ t, At (evI F) ((γ t).1.1 - 1)}

omit [NumberField E] in
theorem incV_mulVec (C : Matrix (Fin n) (Fin r) E) (a : Fin r → E) :
    incV F (C *ᵥ a) = adMat F C *ᵥ incV F a := funext fun i =>
  RingHom.map_mulVec (inclR (F := F) (AF F)) C a i

omit [NumberField E] in
theorem mem_cols {C : Matrix (Fin n) (Fin r) E} {u : Fin n → E} (hu : u ∈ Submodule.span E (Set.range Cᵀ)) :
    ∃ a, C *ᵥ a = u := by
  have e : LinearMap.range C.mulVecLin = Submodule.span E (Set.range Cᵀ) := Matrix.range_mulVecLin C
  rw [← e] at hu
  exact hu

omit [NumberField E] in
theorem span_eq (C : Matrix (Fin n) (Fin r) E) (x : Fin n → AE F E) :
    x ∈ Submodule.span (AE F E) (incV F '' (Submodule.span E (Set.range Cᵀ) : Set (Fin n → E))) ↔
      ∃ a, x = adMat F C *ᵥ a := by
  have e : Submodule.span (AE F E) (incV F '' (Submodule.span E (Set.range Cᵀ) : Set (Fin n → E))) =
      LinearMap.range (adMat F C).mulVecLin := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨a, rfl⟩ := mem_cols hu
      exact ⟨incV F a, (incV_mulVec C a).symm⟩
    · rw [Matrix.range_mulVecLin]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨Cᵀ i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [e]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

omit [NumberField E] in
theorem unipRad_eq (C : Matrix (Fin n) (Fin r) E) : unipRad σ J C =
    unip (HR (AF F) σ J) (Submodule.span E (Set.range Cᵀ)) fun z => (cT (σ : E →+* E) C * J) *ᵥ z = 0 := by
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  obtain ⟨m, hm⟩ : ∃ m : Matrix (Fin n) (Fin n) (AE F E), m = (matHom _ σ J g).1 := ⟨_, rfl⟩
  have hg : cT (sigR (AF F) σ) m * JR (AF F) J * m = JR (AF F) J := hm ▸ g.2
  have key : ((m - 1) * adMat F C = 0 ∧ adMat F (cT (σ : E →+* E) C * J) * (m - 1) = 0 ∧
      ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 → ∃ a : Fin r → AE F E, (m - 1) *ᵥ incV F x = adMat F C *ᵥ a) ↔
      ((∀ u ∈ Submodule.span E (Set.range Cᵀ), m *ᵥ incV F u = incV F u) ∧ ∀ z : Fin n → E,
        (cT (σ : E →+* E) C * J) *ᵥ z = 0 → m *ᵥ incV F z - incV F z ∈
          Submodule.span (AE F E) (incV F '' (Submodule.span E (Set.range Cᵀ) : Set (Fin n → E)))) := by
    simp only [span_eq, sub_mulVec, one_mulVec, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      sub_eq_zero]
    refine ⟨fun ⟨h1, _, h3⟩ => ⟨fun u hu => ?_, h3⟩, fun ⟨h1, h3⟩ => ?_⟩
    · obtain ⟨a, rfl⟩ := mem_cols hu
      rw [incV_mulVec, mulVec_mulVec, h1]
    · have h2 : m * adMat F C = adMat F C := Matrix.ext fun i j =>
        congrFun (h1 (Cᵀ j) (Submodule.subset_span ⟨j, rfl⟩)) i
      refine ⟨h2, ?_, h3⟩
      have e : adMat F (cT (σ : E →+* E) C * J) =
          (cT (sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) := by
        rw [adMat, Matrix.map_mul]; rfl
      rw [e]
      conv_lhs => rw [← h2, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ m), hg]
  subst hm
  exact key

omit [NumberField E] in
theorem idempotent_smul_eq_zero_of_map (x : AE F E) (h : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = 0) : e0 F • x = 0 := by
  have : ∀ x : AE F E, e0 F • x = LinearMap.rTensor E (show Af F →ₗ[F] AF F from LinearMap.inr F (Ainf F) (Af F))
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul a y =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      exact congrArg (· ⊗ₜ[F] y) (Prod.ext (zero_mul _) (one_mul _))
  rw [this, h, map_zero]

omit [NumberField E] in
theorem at_of_projFin {g : GAd σ J} (h : GlobalTheory.AdelicU.projFin σ J g = 1) : At (evI F) ((matHom _ σ J g).1 - 1) := by
  refine (at_iff _).2 (Matrix.ext fun i j => idempotent_smul_eq_zero_of_map _ ?_)
  have e : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((matHom _ σ J g).1 i j) =
      (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j :=
    congrArg (fun y : GFin σ J => (matHom _ σ J y).1 i j) h
  rw [Matrix.sub_apply, map_sub, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem line_of (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    ∃ δ ∈ lines (HR (AF F) σ J), ∀ t, δ (Multiplicative.ofAdd t) = γ t := by
  obtain ⟨w, τ, Z, -, hZ⟩ := hγ
  choose y e1 e2 using hZ
  have hE := isEmbedding_archMat J h τ
  have hi : ∀ a b, archMat σ J τ a = archMat σ J τ b → a = b := fun a b e => hE.injective e
  have h0 : y 0 = 1 := hi _ _ (by rw [e2, zero_smul, NormedSpace.exp_zero, map_one])
  have h1 : ∀ s t, y (s + t) = y s * y t := fun s t => hi _ _ (by
    rw [map_mul, e2, e2, e2, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left s).smul_right t))
  have hc : Continuous y := hE.continuous_iff.2 (by
    have : (matCoord (archMat σ J τ) ∘ y) = fun t : ℝ => NormedSpace.exp (t • Z) := funext e2
    rw [this]
    haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
    have hz : Continuous fun t : ℝ => t • Z := continuous_id.smul continuous_const
    exact (NormedSpace.exp_continuous (𝔸 := Matrix (Fin n) (Fin n) ℂ)).comp hz)
  let δ : Multiplicative ℝ →* GAd σ J :=
    { toFun := fun t => embArch σ J w (y t.toAdd)
      map_one' := by rw [toAdd_one, h0, map_one]
      map_mul' := fun s t => by rw [toAdd_mul, h1, map_mul] }
  exact ⟨δ, ⟨(continuous_embArch σ J w).comp (hc.comp continuous_toAdd),
    fun t => at_of_projFin (projFin_embArch σ J w _)⟩, fun t => (e1 t).symm⟩

theorem level (τ : ∀ w : InfinitePlace F, EmbOver E w) {f : GAd σ J → ℂ} {U : Set (GAd σ J)} (hU : U ∈ 𝓝 1)
    (hf : ∀ u ∈ U, (∀ w, (matHom _ σ J u).1.map (piInf (τ w)) = 1) → ∀ h, f (h * u) = f h) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ J
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean (ofFin σ J ⁻¹' U)
    ((continuous_ofFin σ J).continuousAt.preimage_mem_nhds (by rwa [map_one]))
  refine ⟨V.1.comap (GlobalTheory.AdelicU.projFin σ J), V.isOpen.preimage (continuous_projFin σ J), fun k hk hk' => hf k ?_ fun w => ?_⟩
  · have := ofInf_projInf_mul_ofFin_projFin σ J k
    rw [mem_finPts.1 hk', map_one, one_mul] at this
    rw [← this]
    exact hV hk
  · change archMat σ J (τ w) (projArch σ J w k) = 1
    rw [← projInfArch_projInf, mem_finPts.1 hk', map_one, map_one]

def linesG (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : Set (Multiplicative ℝ →* GAd σ J) := lines (HR (AF F) σ J)

theorem line_ofG (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    ∃ δ ∈ linesG σ J, γ = fun t => δ (Multiplicative.ofAdd t) :=
  let ⟨δ, a, b⟩ := line_of h hγ
  ⟨δ, a, funext fun t => (b t).symm⟩

theorem moderate (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (f : GAd σ J → ℂ)
    (h1 : ∀ γ ∈ ratPts σ J, ∀ g, f (γ * g) = f g)
    (h2 : ∃ (k : ℕ) (S : Set (GAd σ J → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧
      (∃ C : ℝ, ∀ g, ‖f₁ g‖ ≤ C * (height σ J g : ℝ) ^ k) ∧
      ∀ γ ∈ linesG σ J, ∃ f₂ ∈ S, ∀ g, HasDerivAt (fun t : ℝ => f₁ (g * γ (Multiplicative.ofAdd t))) (f₂ g) 0)
    (h3 : ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GAd σ J)), (∀ i, γ i ∈ linesG σ J) → ∀ g,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod))
    (h4 : ∃ U ∈ 𝓝 (1 : GAd σ J), ∀ u ∈ U, (∀ w, (matHom _ σ J u).1.map (piInf (τ w)) = 1) → ∀ g, f (g * u) = f g) :
    IsSmoothModerate σ J f := by
  obtain ⟨k, S, hf, hSS⟩ := h2
  obtain ⟨U, hU, hU'⟩ := h4
  refine ⟨h1, level τ hU hU', (hSS f hf).1, fun k γ hγ g => ?_, k, fun l hl => ?_⟩
  · choose δ hδ e using fun i => line_ofG h (hγ i)
    obtain rfl : γ = fun i t => δ i (Multiplicative.ofAdd t) := funext e
    exact h3 k δ hδ g
  · have : l.foldr lineDer f ∈ S := by
      induction l with
      | nil => exact hf
      | cons γ l ih =>
        obtain ⟨δ, hδ, e⟩ := line_ofG h (hl γ List.mem_cons_self)
        obtain ⟨f₂, a1, a2⟩ := (hSS _ (ih fun β hβ => hl β (List.mem_cons_of_mem _ hβ))).2.2 δ hδ
        have e2 : lineDer γ (l.foldr lineDer f) = f₂ := funext fun g => by
          rw [e]
          exact (a2 g).deriv
        rw [List.foldr_cons, e2]
        exact a1
    exact (hSS _ this).2.1

theorem cuspidal (f : GAd σ J → ℂ)
    (h5 : ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E), 0 < r → LinearIndependent E Cᵀ → cT (σ : E →+* E) C * J * C = 0 →
      Van (rat (HR (AF F) σ J))
        (unip (HR (AF F) σ J) (Submodule.span E (Set.range Cᵀ)) fun z => (cT (σ : E →+* E) C * J) *ᵥ z = 0) f) :
    IsCuspidal σ J f := fun r C hC => by
  have := h5 r C hC.1 hC.2.1 hC.2.2
  rw [← unipRad_eq, ← ratPts_eq] at this
  exact this

theorem rapidG (hS : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J) (f : GAd σ J → ℂ)
    (hm : IsSmoothModerate σ J f) (hc : IsCuspidal σ J f) (N : ℕ) :
    ∃ C : ℝ, ∀ g, ∃ γ ∈ ratPts σ J, ‖f g‖ * (height σ J (γ * g) : ℝ) ^ N ≤ C := by
  obtain ⟨S₀, -, hcov, -, -, hφ⟩ := exists_cover hS h hJ
  obtain ⟨C, hC⟩ := (hφ f hm hc N).1
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, rfl⟩ := hcov g
  refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
  rw [inv_mul_cancel_left, hm.left γ hγ]
  exact hC s hs

theorem core (hS : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Subgroup (GL (Fin n) (AE F E))) (hH : H = HR (AF F) σ J) (f : H → ℂ)
    (h1 : ∀ γ ∈ rat H, ∀ g, f (γ * g) = f g)
    (h2 : ∃ (k : ℕ) (S : Set (H → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧ (∃ C : ℝ, ∀ g, ‖f₁ g‖ ≤ C * (heightGL F g.1 : ℝ) ^ k) ∧
      ∀ γ ∈ lines H, ∃ f₂ ∈ S, ∀ g, HasDerivAt (fun t : ℝ => f₁ (g * γ (Multiplicative.ofAdd t))) (f₂ g) 0)
    (h3 : ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* H)), (∀ i, γ i ∈ lines H) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod))
    (h4 : ∃ U ∈ 𝓝 (1 : H), ∀ u ∈ U, (∀ w, u.1.1.map (piInf (τ w)) = 1) → ∀ g, f (g * u) = f g)
    (h5 : ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E), 0 < r → LinearIndependent E Cᵀ → cT (σ : E →+* E) C * J * C = 0 →
      Van (rat H) (unip H (Submodule.span E (Set.range Cᵀ)) fun z => (cT (σ : E →+* E) C * J) *ᵥ z = 0) f)
    (N : ℕ) : ∃ C : ℝ, ∀ g, ∃ γ ∈ rat H, ‖f g‖ * (heightGL F (γ * g).1 : ℝ) ^ N ≤ C := by
  subst hH
  have h6 := cuspidal f h5
  rw [← ratPts_eq] at h1 ⊢
  exact rapidG hS h hJ f (moderate h τ f h1 h2 h3 h4) h6 N

end CuspR

open CuspR in
theorem cuspRapid_of (hS : GlobalTheory.Published.SiegelSetUnitary) (hU : UMGSmooth) : CuspRapid := by
  intro F E _ _ _ _ _ σ h τ d W hJ f h1 h2 h4 h5 N
  have hσ := sigma_sigma h
  obtain ⟨c, hc, hJ'⟩ := exists_herm h hJ
  obtain ⟨C, hC⟩ := core hS h hJ' τ (UG (cA σ) (incM F W.J)) (ug_eq_hr hσ hc) f h1 h2 (hU F E σ h τ d W hJ f h2) h4
    (fun r C hr hl hi => by
      have e : (fun z => (cT (σ : E →+* E) C * (c • W.J.map σ)) *ᵥ z = 0) =
          fun z => ∀ u ∈ Submodule.span E (Set.range Cᵀ), form σ W.J z u = 0 :=
        funext fun z => propext (perp_iff hσ hJ hc C z).symm
      rw [e]
      refine h5 _ (fun h0 => ?_) fun u hu => (perp_iff hσ hJ hc C u).2 ?_
      · exact hl.ne_zero ⟨0, hr⟩ ((Submodule.eq_bot_iff _).1 h0 _ (Submodule.subset_span ⟨_, rfl⟩))
      · obtain ⟨a, rfl⟩ := mem_cols hu
        rw [mulVec_mulVec, hi, zero_mulVec]) N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, e⟩ := hC g
  refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) (norm_nonneg _)) e
  exact NNReal.coe_le_coe.2 (ciInf_le' (fun γ : ratU σ W.J => ht (γ.1 * g)) ⟨γ, hγ⟩)

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_soFin (hF : SoFin) (hp : IsPair B M χX χW om r s r' s') {m : ℕ} (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hφ : ∀ j, φ j ∈ SB _) : ∃ ψ : Fin m → (Fin n × Fin d → Af F) → ℂ, (∀ j, ψ j ∈ soFin B M) ∧
      ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
        ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (soCoeff (B := B) M φ)
  let P := Submodule.linearProjOfIsCompl _ _ hQ
  let ψ : Fin m → (Fin n × Fin d → Af F) → ℂ := fun j => ∑ i, (P (Pi.single j 1) : Fin m → ℂ) i • φ i
  have hψ : ∀ j, ψ j ∈ soFin B M := fun j =>
    ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i), (P (Pi.single j 1)).2⟩
  have key : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := fun w hw => by
    obtain ⟨m', f', χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 _ hw
    have hmem : ∀ x, (fun j => w j x) ∈ soCoeff (B := B) M φ := fun x f₀ => by
      have e2 : ∑ j, w j x • φ j = ∑ i, f' i x • χ i := by
        funext y
        obtain ⟨z, hz1, hz2⟩ : ∃ z : Fin n × Fin d → AdeleRing (𝓞 F) F,
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = x ∧ (fun i => (z i).2) = y :=
          ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),
            funext fun i => RingEquiv.apply_symm_apply _ _, rfl⟩
        have := congrFun e z
        simp only [Finset.sum_apply, pureA, hz1, hz2] at this
        simpa [Finset.sum_apply] using this
      have e3 : pureA F f₀ (∑ i, f' i x • χ i) = ∑ i, f' i x • pureA F f₀ (χ i) := by
        funext z; simp [pureA, Finset.mul_sum, Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2, e3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((hχ i).2 f₀)
    funext z
    set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
    have e4 : (fun j => w j x) = ∑ j, w j x • (P (Pi.single j 1) : Fin m → ℂ) := by
      have a1 : (P (fun j => w j x) : Fin m → ℂ) = fun j => w j x :=
        congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, hmem x⟩)
      have a2 : (fun j => w j x) = ∑ j, w j x • (Pi.single j 1 : Fin m → ℂ) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [← a1, a2]
      simp
    have e5 : ∀ i, w i x = ∑ j, w j x * (P (Pi.single j 1) : Fin m → ℂ) i := fun i => by
      simpa [Finset.sum_apply] using congrFun e4 i
    simp only [Finset.sum_apply, pureA, ψ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = _ from e5 i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  exact ⟨ψ, hψ, key⟩

theorem polData_sum (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb) ∧ (∀ i, φ i ∈ SB _) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, x, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f hf χ h1 h2 h3 using fun i => (x i).2
  refine ⟨m, fun i => c i • f i, fun i => FiniteAdelicSupportCompactness.pf (χ i), fun i => Submodule.smul_mem _ _ (hf i),
    fun i => FiniteAdelicSupportCompactness.pf_mem ⟨h1 i, ((h2 i).and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩,
    Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h3 i, FiniteAdelicSupportCompactness.pure_eq]
  funext z
  simp [pureA, mul_assoc]

variable (B W) in

def Nice (f : UA σ W.J → ℂ) : Prop := LeftInv f ∧ UMG W f ∧ SmoothFin W B.emb f

theorem nice_zero : Nice B W (0 : UA σ W.J → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨0, {0}, rfl, by
    rintro _ rfl
    exact ⟨continuous_const, ⟨0, fun h => by simp⟩, fun γ _ => ⟨0, rfl, fun h => hasDerivAt_const _ _⟩⟩⟩,
    Set.univ, univ_mem, fun _ _ _ _ => rfl⟩

theorem Nice.lin (hU : UMGLin) (hc : IsCMExt F E σ) (hJ : EpsHerm σ W.J) {f f' : UA σ W.J → ℂ} (h : Nice B W f)
    (h' : Nice B W f') (a b : ℂ) : Nice B W (a • f + b • f') := by
  refine ⟨fun γ hγ x => ?_, hU F E σ hc B.emb d W hJ f f' h.2.1 h'.2.1 a b, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, h.1 γ hγ x, h'.1 γ hγ x]
  · obtain ⟨U, hU1, hu⟩ := h.2.2
    obtain ⟨U', hU1', hu'⟩ := h'.2.2
    refine ⟨U ∩ U', inter_mem hU1 hU1', fun u hm h1 x => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, hu u hm.1 h1 x, hu' u hm.2 h1 x]

theorem nice_sum (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hp : IsPair B M χX χW om r s r' s')
    {𝓕} (hD : Dom M om 𝓕) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hf : ∀ i, f i ∈ M.Pol B.ψ B.emb) (hφ : ∀ i, φ i ∈ 𝓕) (hsb : ∀ i, φ i ∈ SB _) :
    Nice B W (M.I om (∑ i, pureA F (f i) (φ i))) := by
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  have e : M.I om (∑ i, pureA F (f i) (φ i)) = ∑ i, M.I om (pureA F (f i) (φ i)) :=
    funext fun h => ((dom_sum hB hp hD f φ hφ hsb).2.2 h).trans (Finset.sum_apply _ _ _).symm
  rw [e]
  refine Finset.sum_induction _ _ (fun a b ha hb => by simpa using ha.lin hU hp.base.cm hJ hb 1 1) nice_zero fun i _ => ?_
  exact ⟨(hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem _ (hsb i))).1,
    hG F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hD _ (hφ i) (hsb i) _ (hf i)⟩

end

theorem sig_nice (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (ht' : IsTriple B G X om om') {f : UA σ G.W.J → ℂ} (hf : f ∈ PositivityTheory.ThKEnd.Sig B G om om') :
    Nice B G.W f := by
  obtain ⟨h1, h2, h3⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  obtain ⟨m, f, φ, c1, c2, rfl⟩ := polData_sum h1 hΦ
  obtain ⟨m', f', φ', c1', c2', rfl⟩ := polData_sum h2 hΦ'.1
  obtain ⟨ψ, hψ, hk⟩ := exists_soFin hF h2 φ' c2'
  rw [hk f' hΦ'.2]
  have n1 := nice_sum hB hU hE hG hI h1 (hW F E σ B _ _ _ _ _ _ _ om _ _ _ _ h1 (Or.inl h3)) f φ c1 c2 c2
  have n2 := nice_sum hB hU hE hG hI h2 (dom_of_domSoU hS h2) f' ψ c1' hψ fun i => (hψ i).1
  simpa [sub_eq_add_neg] using n1.lin hU h1.base.cm hJ n2 1 (-1)

theorem sigRapid_of (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) (hC : CuspRapid) : PositivityTheory.ThKEnd.Orth.SigRapid := by
  intro F E _ _ _ _ _ σ B a a' G X om om' ht' f hf hc
  obtain ⟨n1, n2, n3⟩ := sig_nice hB hU hE hG hI hT hW hS hF ht' hf
  obtain ⟨h1, -, -⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  refine ⟨?_, n1, hC F E σ h1.base.cm B.emb _ G.W hJ f n1 n2 n3 hc⟩
  obtain ⟨k, S, hS1, hS2⟩ := n2
  exact (hS2 f hS1).1

end PositivityTheory.ThKEst

end
end

section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem umgSmooth : UMGSmooth := umgSmooth_of (linDer_of lineGen_of lineEx_of) lineGen_of

theorem cuspRapid (h : GlobalTheory.Published.SiegelSetUnitary) : CuspRapid := cuspRapid_of h umgSmooth

theorem level : Level := level_of coefEq_of fourierInj_of (coefBd_of coefReal_of)

theorem iDer (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IDer := iDer_of hB hO hL (iInv_of hB)

theorem iUMG (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IUMG :=
  iUMG_of hB grpTop_of epsOf_of (iDer hB hO hL) level (iInv_of hB)

theorem sigRapid (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) :
    PositivityTheory.ThKEnd.Orth.SigRapid :=
  sigRapid_of hB umgLin_of epsOf_of (iUMG hB hO hL) (iInv_of hB) Sq.triplePair_holds (domWeil_of_U (domWeilU h)) (domSoU h)
    soFin_of (cuspRapid h)

end PositivityTheory.ThKEst

end
end
