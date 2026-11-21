import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGapsStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasicStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesParameterUnique
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRepStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsFRepDualStandardUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRepStatement

section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.discrete_series_parameter_unique : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  first | exact @GlobalTheory.DSInequiv.param_eq_of_equiv | exact GlobalTheory.DSInequiv.param_eq_of_equiv | (intros; apply GlobalTheory.DSInequiv.param_eq_of_equiv <;> assumption)
end Gp91
end

section
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensForm

theorem common_bound {ι α β : Type} [DecidableEq ι] (P : α → Prop) (S : Set β) (n : α → β → ℝ)
    (hn : ∀ a v, 0 ≤ n a v) (f : ι → β → ℝ)
    (h : ∀ c, ∃ (C : ℝ) (L : List α), (∀ a ∈ L, P a) ∧ ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum)
    (s : Finset ι) :
    ∃ (C : ℝ) (L : List α), 0 ≤ C ∧ (∀ a ∈ L, P a) ∧
      ∀ c ∈ s, ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum := by
  have hs : ∀ (L : List α) v, 0 ≤ (L.map fun a => n a v).sum := by
    intro L v
    apply List.sum_nonneg
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hn a v
  induction s using Finset.induction_on with
  | empty => exact ⟨0, [], le_rfl, by simp, by simp⟩
  | insert c s _ ih =>
    obtain ⟨C, L, hC, hL, hb⟩ := ih
    obtain ⟨C', L', hL', hb'⟩ := h c
    refine ⟨C + |C'|, L ++ L', by positivity, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hL a ha
      · exact hL' a ha
    · intro d hd v hv
      rw [List.map_append, List.sum_append]
      have h1 := hs L v
      have h2 := hs L' v
      have h3 := abs_nonneg C'
      have h4 := le_abs_self C'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · have := hb' v hv
        nlinarith [mul_nonneg hC h1, mul_nonneg hC h2, mul_nonneg h3 h1,
          mul_le_mul_of_nonneg_right h4 h2]
      · have := hb d hd v hv
        nlinarith [mul_nonneg hC h2, mul_nonneg h3 h1, mul_nonneg h3 h2]

variable {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hh_act (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r)
    (hρ : (ρ g)ᴴ * Γ * ρ g = Γ) (hσ : ∀ v, ‖R.σ g v‖ = ‖v‖) (x y : ι → R.H) :
    hh Γ R (act ρ R g x) (act ρ R g y) = hh Γ R x y := by
  have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 hσ
  conv_rhs => rw [← hρ]
  simp only [hh, act, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hiso, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ b, ∑ a, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ a, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [RCLike.star_def]
        ring

omit [DecidableEq ι] in

theorem norm_hh_le (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) (A B : ℝ)
    (hx : ∀ c, ‖x c‖ ≤ A) (hy : ∀ c, ‖y c‖ ≤ B) :
    ‖hh Γ R x y‖ ≤ (∑ i, ∑ j, ‖Γ i j‖) * (A * B) := by
  rw [hh, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)
  rw [mul_comm A B]
  exact mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))

theorem family_bound (R R' : Rep k r) (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ c, ∀ v ∈ R.sm, ‖T c v‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖).sum := by
  obtain ⟨C, L, -, hL, hb⟩ := common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm
    (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _)
    (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ
  exact ⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩

theorem pulledBack_isInvForm : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y _
    simp only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]
  · intro a x hx y _
    simp only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro x _ y hy y' hy'
    simp only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro a x _ y hy
    simp only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring
  · intro g hg x hx y hy
    show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _
    rw [hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]
    exact hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _
  · obtain ⟨C, Ws, hW, hb⟩ := family_bound (RI I) R (io I) (hT.io_sm I)
    obtain ⟨C', Ws', hW', hb'⟩ := family_bound (RI J) R (io J) (hT.io_sm J)
    refine ⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩
    · intro W hWm
      rcases List.mem_append.1 hWm with h | h
      · exact hW W h
      · exact hW' W h
    · intro x hx y hy
      refine (norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)
      ring

end GlobalTheory.TensForm
end Gp91
end

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_decomposition_parameters : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  atlas_forward_decl GlobalTheory.TensForm.pulledBack_isInvForm
end Gp91
end

section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensOrth

variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem hh_smul (Γ : Matrix ι ι ℂ) (R : Rep k r) (a b : ℂ) (x y : ι → R.H) :
    hh Γ R (fun c => a • x c) (fun c => b • y c) = a * star b * hh Γ R x y := by
  simp only [hh, inner_smul_left, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (x : ι → R.H) (y : κ → ι → R.H) :
    hh Γ R x (fun c => ∑ J, y J c) = ∑ J, hh Γ R x (y J) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem hh_star (Γ : Matrix ι ι ℂ) (hΓ : Γᴴ = Γ) (R : Rep k r) (x y : ι → R.H) :
    star (hh Γ R x y) = hh Γ R y x := by
  simp only [hh, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (Γ j i) = Γ i j := by
    have := congrFun (congrFun hΓ i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [h]
  congr 1
  exact inner_conj_symm _ _

theorem eq_zero_of_hh (Γ : Matrix ι ι ℂ) (hΓ : Γ * Γ = 1) (R : Rep k r) (x : ι → R.H)
    (h : hh Γ R x (fun c => ∑ j, Γ c j • x j) = 0) (c : ι) : x c = 0 := by
  set z : ι → R.H := fun c => ∑ j, Γ c j • x j with hz
  have h1 : hh Γ R x z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    unfold hh
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ⟪z i, z i⟫_ℂ = ∑ j, Γ i j * ⟪z i, x j⟫_ℂ := by
      conv_lhs => enter [3]; rw [hz]
      simp only [inner_sum, inner_smul_right]
    rw [← this, inner_self_eq_norm_sq_to_K]
    rfl
  rw [h1, Complex.ofReal_eq_zero] at h
  have h2 : ∀ i, z i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖z i‖)).1 h i (mem_univ _)
    simpa using this
  have h3 : ∑ i, Γ c i • z i = x c := by
    simp only [hz, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, hΓ, Matrix.one_apply]
    simp
  rw [← h3]
  simp [h2]

theorem SmMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have := hT.smul 0 0 R.smSub.zero_mem
  simpa using this

omit [DecidableEq ι] [DecidableEq κ] in
theorem raw_scale {ρ : Mx k r → Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
    {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} (h : TensRaw ρ R RI io pr)
    (a : κ → ℂ) (ha : ∀ I, a I ≠ 0)
    (h1 : ∀ I c, SmMap (RI I) R (fun v => a I • io I c v))
    (h2 : ∀ I c, SmMap R (RI I) (fun v => (a I)⁻¹ • pr I c v)) :
    TensRaw ρ R RI (fun I c v => a I • io I c v) (fun I c v => (a I)⁻¹ • pr I c v) where
  io_sm := h1
  pr_sm := h2
  io_eq := fun I g hg y hy => by
    funext c
    have := congrFun (h.io_eq I g hg y hy) c
    simp only [act] at this ⊢
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_comm]
  pr_eq := fun I g hg x hx => by
    rw [← Finset.smul_sum, ← Finset.smul_sum, map_smul, h.pr_eq I g hg x hx]
  sum_io_pr := fun x hx c => by
    rw [← h.sum_io_pr x hx c]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hm : ∑ d, pr I d (x d) ∈ (RI I).smSub :=
      Submodule.sum_mem _ fun d _ => (h.pr_sm I d).mem _ (hx d)
    rw [← Finset.smul_sum, (h.io_sm I c).smul _ _ hm, smul_smul, mul_inv_cancel₀ (ha I), one_smul]
  pr_io := fun I y hy => by
    conv_rhs => rw [← h.pr_io I y hy]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h.pr_sm I c).smul _ _ ((h.io_sm I c).mem _ hy), smul_smul, inv_mul_cancel₀ (ha I), one_smul]
  pr_io_ne := fun I J hIJ y hy => by
    have : ∀ c, (a I)⁻¹ • pr I c (a J • io J c y) = ((a I)⁻¹ * a J) • pr I c (io J c y) := fun c => by
      rw [(h.pr_sm I c).smul _ _ ((h.io_sm J c).mem _ hy), smul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h.pr_io_ne I J hIJ y hy, smul_zero]

theorem tensH_of_raw : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hinj hF hT
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : PoulsenG := hH.2.2.2.2.2.1
  have hform := GlobalTheory.T.tensor_decomposition_parameters hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  have horth : ∀ I J, I ≠ J → ∀ y ∈ (RI I).sm, ∀ y' ∈ (RI J).sm,
      hh Γ R (fun c => io I c y) (fun c => io J c y') = 0 := by
    intro I J hIJ
    rcases (hP k r ε _ _ _ _ (hRI I) (hRI J)).2 _ (hform I J) with h | ⟨U, hU⟩
    · exact h
    · exact absurd (hinj (GlobalTheory.T.discrete_series_parameter_unique hH k r ε _ _ _ _ (hRI I) (hRI J) U hU)) hIJ
  choose cI hc using fun I => (hP k r ε _ _ _ _ (hRI I) (hRI I)).1 _ (hform I I)
  have hunit : ∀ I, ∃ w ∈ (RI I).sm, ‖w‖ = 1 := fun I => by
    obtain ⟨-, -, -, -, h5, -, h7, ⟨w, hw, hwK, -⟩, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε _ _ (hRI I)
    exact ⟨w, h5 w (h7 w hwK), hw⟩
  have hreal : ∀ I, ((cI I).re : ℂ) = cI I := fun I => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have h1 := hc I w hw w hw
    have h2 := hh_star Γ hF.1 R (fun c => io I c w) (fun c => io I c w)
    rw [inner_self_eq_norm_sq_to_K, hn] at h1
    simp only [map_one, one_pow, mul_one] at h1
    rw [h1] at h2
    exact Complex.conj_eq_iff_re.1 h2
  have hne : ∀ I, cI I ≠ 0 := fun I h0 => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have hx : ∀ c, (∑ j, Γ c j • io I j w) ∈ R.smSub := fun c =>
      Submodule.sum_mem _ fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ hw)
    have hz : hh Γ R (fun c => io I c w) (fun c => ∑ j, Γ c j • io I j w) = 0 := by
      have e : (fun c => ∑ j, Γ c j • io I j w) =
          fun c => ∑ J, io J c (∑ e, pr J e (∑ j, Γ e j • io I j w)) :=
        funext fun c => (hT.sum_io_pr _ hx c).symm
      rw [e, hh_sum_right]
      refine Finset.sum_eq_zero fun J _ => ?_
      have hm : ∑ e, pr J e (∑ j, Γ e j • io I j w) ∈ (RI J).smSub :=
        Submodule.sum_mem _ fun e _ => (hT.pr_sm J e).mem _ (hx e)
      by_cases hIJ : I = J
      · subst hIJ
        have := hc I w hw _ hm
        rw [h0, zero_mul] at this
        exact this
      · exact horth I J hIJ w hw _ hm
    have h0' := eq_zero_of_hh Γ hF.2.1 R _ hz
    have h1 := hT.pr_io I w hw
    simp only [h0', SmMap_zero (hT.pr_sm I _), Finset.sum_const_zero] at h1
    rw [← h1, norm_zero] at hn
    exact zero_ne_one hn
  have hre : ∀ I, (cI I).re ≠ 0 := fun I h => hne I (by rw [← hreal I, h]; simp)
  have hsc : ∀ (m m' : Fin (2 * r + k + 1) → ℝ) (S S' : Rep k r), S.IsDG ε m → S'.IsDG ε m' →
      ∀ (T : S.H → S'.H) (a : ℂ), SmMap S S' T → SmMap S S' (fun v => a • T v) := by
    intro m m' S S' hS hS' T a h
    have := (GlobalTheory.T.smooth_maps_closure hK k r ε _ _ _ S S' S' hS hS' hS').2.2.1 T T (a - 1) h h
    simpa only [sub_smul, one_smul, sub_add_cancel] using this
  set a : κ → ℂ := fun I => (((Real.sqrt |(cI I).re|)⁻¹ : ℝ) : ℂ) with ha
  have hane : ∀ I, a I ≠ 0 := fun I => by
    simp only [ha, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (abs_pos.2 (hre I))).ne'
  refine ⟨fun I c v => a I • io I c v, fun I c v => (a I)⁻¹ • pr I c v,
    fun I => (cI I).re / |(cI I).re|, ⟨raw_scale hT a hane
      (fun I c => hsc _ _ _ _ (hRI I) hR _ _ (hT.io_sm I c))
      (fun I c => hsc _ _ _ _ hR (hRI I) _ _ (hT.pr_sm I c)), fun I => ?_, fun I y hy y' hy' => ?_,
      fun I J hIJ y hy y' hy' => ?_⟩⟩
  · rcases lt_or_gt_of_ne (hre I) with h | h
    · right
      rw [abs_of_neg h, div_neg, div_self (hre I)]
    · left
      rw [abs_of_pos h, div_self (hre I)]
  · have h1 := hc I y hy y' hy'
    rw [hh_smul, h1, ← mul_assoc]
    congr 1
    have h2 : (Real.sqrt |(cI I).re|)⁻¹ * (Real.sqrt |(cI I).re|)⁻¹ * (cI I).re = (cI I).re / |(cI I).re| := by
      rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_inv_mul]
    rw [← h2]
    simp only [ha, RCLike.star_def, Complex.conj_ofReal]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hreal I]
  · rw [hh_smul, horth I J hIJ y hy y' hy', mul_zero]

end GlobalTheory.TensOrth
end
end Gp91
end

section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_decomposition_injective_parameters : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  first | exact @GlobalTheory.TensOrth.tensH_of_raw | exact GlobalTheory.TensOrth.tensH_of_raw | (intros; apply GlobalTheory.TensOrth.tensH_of_raw <;> assumption)
end Gp91
end

section
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensExists

theorem l1_add_le {n : ℕ} (x y : Fin n → ℤ) : n1 (x + y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem l1_sub_le {n : ℕ} (x y : Fin n → ℤ) : n1 (x - y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem n1_eZ_eq_card {n : ℕ} (I : Finset (Fin n)) : n1 (eZ I) = I.card := by
  unfold n1 eZ
  have : ∀ i : Fin n, (if i ∈ I then (1 : ℤ) else 0).natAbs = if i ∈ I then 1 else 0 := by
    intro i; split_ifs <;> rfl
  simp [this]

theorem l1_single {n : ℕ} (s : Fin n) : n1 (Pi.single s (1 : ℤ)) = 1 := by
  unfold n1
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem addSet_inj {n l : ℕ} (mu : Fin n → ℝ) : Function.Injective (fun I : Sub n l => addSet mu I.1) := by
  intro I J hIJ
  apply Subtype.ext
  ext a
  have h := congrFun hIJ a
  simp only [addSet, add_right_inj] at h
  by_cases h1 : a ∈ I.1 <;> by_cases h2 : a ∈ J.1 <;> simp_all

theorem sub_single_inj {n : ℕ} (mu : Fin n → ℝ) :
    Function.Injective (fun s : Fin n => mu - (Pi.single s 1 : Fin n → ℝ)) := by
  intro s t hst
  by_contra hne
  have h := congrFun hst s
  simp [Pi.single_apply, hne] at h

theorem tens_exists : HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFamG lam q0 R → ∀ ν, (∀ l, n1 ν + l ≤ q0 → ∃ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep) ∧ (n1 ν + 1 ≤ q0 → ∃ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep) := by
  intro hH k r lam u b bv ga h q0 R hN hF ν
  have hZ : ZuckG := hH.2.2.2.2.1
  have hnum := (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).2 ν
  constructor
  · intro l hl
    have h0 : n1 ν ≤ q0 := by omega
    have hR := hF ν h0
    have hI : ∀ I : Sub (2 * r + k + 1) l, (R (ν + eZ I.1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
        (addSet (fun a => lam a + (ν a : ℝ)) I.1) := by
      intro I
      have h1 : n1 (ν + eZ I.1) ≤ q0 := by
        have := l1_add_le ν (eZ I.1)
        rw [n1_eZ_eq_card, I.2] at this
        omega
      have h2 := hF _ h1
      have e : (fun a => lam a + (((ν + eZ I.1) a : ℤ) : ℝ)) = addSet (fun a => lam a + (ν a : ℝ)) I.1 := by
        funext a
        simp only [addSet, eZ, Pi.add_apply]
        split_ifs <;> push_cast <;> ring
      rwa [e] at h2
    obtain ⟨io, pr, hT⟩ := (hZ k r _ lam q0 R hF ν).1 l hl
    exact GlobalTheory.T.tensor_decomposition_injective_parameters hH k r _ _ _ _ l _ _ io pr _ _ _ hR hI (addSet_inj _) (GlobalTheory.T.isFRep_exteriorPower_standardRep k r l) hT
  · intro hl
    have h0 : n1 ν ≤ q0 := by omega
    have hR := hF ν h0
    have hI : ∀ s : Fin (2 * r + k + 1), (R (ν - Pi.single s 1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
        ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := by
      intro s
      have h1 : n1 (ν - Pi.single s 1) ≤ q0 := by
        have := l1_sub_le ν (Pi.single s 1)
        rw [l1_single] at this
        omega
      have h2 := hF _ h1
      have e : (fun a => lam a + (((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
          (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
        funext a
        simp only [Pi.sub_apply, Pi.single_apply]
        split_ifs <;> push_cast <;> ring
      rwa [e] at h2
    obtain ⟨io, pr, hT⟩ := (hZ k r _ lam q0 R hF ν).2 hl
    exact GlobalTheory.T.tensor_decomposition_injective_parameters hH k r _ _ _ _ 1 _ _ io pr _ _ _ hR hI (sub_single_inj _) (GlobalTheory.T.isFRep_dual_standard_unitaryRep k r) hT

end GlobalTheory.TensExists
end Gp91
end

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.pieri_tensor_decomposition : HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFamG lam q0 R → ∀ ν, (∀ l, n1 ν + l ≤ q0 → ∃ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep) ∧ (n1 ν + 1 ≤ q0 → ∃ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep) := by
  atlas_forward_decl GlobalTheory.TensExists.tens_exists
end Gp91
end
