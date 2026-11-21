import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivatives
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAvgClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRankOneIsAvg

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  first | exact @GlobalTheory.AvgFam.avg_closed | exact GlobalTheory.AvgFam.avg_closed | (intros; apply GlobalTheory.AvgFam.avg_closed <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealAverage

open GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {K : Type} [TopologicalSpace K] {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem continuous_atTau (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    Continuous fun k => atTau θ V τ (κ k) :=
  (continuousOn_atTau hθ V τ).comp_continuous hκ hU

theorem continuous_infMat_atTau (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (τ' : D.what₂.Tau) : Continuous fun k => infMat D.sp.cm.sig V.gram (θ τ') (atTau θ V τ (κ k)) := by
  by_cases c : τ' = τ
  · subst c
    exact hκ.congr fun k => ((atTau_spec hθ V τ' (hU k)).2.1).symm
  · exact continuous_const.congr fun k => ((atTau_spec hθ V τ (hU k)).2.2 τ' c).symm

theorem continuous_infMat_atTau_inv (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ' : D.what₂.Tau) :
    Continuous fun k => infMat D.sp.cm.sig V.gram (θ τ') (atTau θ V τ (κ k))⁻¹ := by
  by_cases c : τ' = τ
  · subst c
    have c1 : Continuous fun k => (gramAt D V τ')⁻¹ * (κ k)ᴴ * gramAt D V τ' :=
      (continuous_const.matrix_mul hκ.matrix_conjTranspose).matrix_mul continuous_const
    exact c1.congr fun k => ((isAtTau_inv V τ' (hU k) (atTau_spec hθ V τ' (hU k))).2.1).symm
  · exact continuous_const.congr fun k => ((isAtTau_inv V τ (hU k) (atTau_spec hθ V τ (hU k))).2.2 τ' c).symm

theorem continuous_normInf_atTau (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : Continuous fun k => normInf θ V (atTau θ V τ (κ k)) := by
  unfold normInf
  refine continuous_finset_sum _ fun τ' _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_infMat_atTau hθ hκ hU τ').matrix_elem i j).norm).add
    (((continuous_infMat_atTau_inv hθ hκ hU τ').matrix_elem i j).norm)

theorem continuous_adAt_atTau (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ' : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Continuous fun k => adAt θ (atTau θ V τ (κ k)) τ' X :=
  ((continuous_infMat_atTau_inv hθ hκ hU τ').matrix_mul continuous_const).matrix_mul
    (continuous_infMat_atTau hθ hκ hU τ')

variable (θ V τ κ) in

def famSpan (𝒟 : Set (GA D V → ℂ)) : Submodule ℂ (K → GA D V → ℂ) :=
  Submodule.span ℂ {F | ∃ c : K → ℂ, Continuous c ∧ ∃ ψ ∈ 𝒟, F = fun k x => c k * ψ (x * atTau θ V τ (κ k))}

section Fam

variable {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
  (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ)
include hθ hκ hU h𝒟

theorem famSpan_cont : ∀ F ∈ famSpan θ V τ κ 𝒟, Continuous fun p : K × GA D V => F p.1 p.2 := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    exact (hc.comp continuous_fst).mul
      ((h𝒟 ψ hψ).cont.comp (continuous_snd.mul ((continuous_atTau hθ hκ hU).comp continuous_fst)))
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

omit hκ in
theorem famSpan_sm : ∀ F ∈ famSpan θ V τ κ 𝒟, ∀ k, F k ∈ SmFun θ V := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    intro k
    exact (SmFun θ V).smul_mem (c k) (rTr_mem hθ (isRealPt_atTau hθ τ (hU k)) (h𝒟 ψ hψ).smooth)
  | zero => exact fun _ => zero_mem _
  | add x y _ _ hx hy => exact fun k => add_mem (hx k) (hy k)
  | smul a x _ hx => exact fun k => (SmFun θ V).smul_mem a (hx k)

end Fam

section Der

variable {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
  (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ)
  (hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟)
include hθ hκ hU h𝒟 hR

theorem famSpan_Rder_gen {c : K → ℂ} (hc : Continuous c) {ψ : GA D V → ℂ} (hψ : ψ ∈ 𝒟) (τ' : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ') :
    (fun k => Rder θ V τ' X (fun x => c k * ψ (x * atTau θ V τ (κ k)))) ∈ famSpan θ V τ κ 𝒟 := by
  set Z : Fin V.rank × Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun a => Matrix.single a.1 a.2 1
  set X1 := fun a => (1 / 2 : ℂ) • (Z a + conjAt V τ' (Z a))
  set X2 := fun a => (1 / (2 * Complex.I) : ℂ) • (Z a - conjAt V τ' (Z a))
  set Y := fun k => adAt θ (atTau θ V τ (κ k)) τ' X
  have e : (fun k => Rder θ V τ' X (fun x => c k * ψ (x * atTau θ V τ (κ k)))) =
      ∑ a : Fin V.rank × Fin V.rank, ((fun k x => (c k * Y k a.1 a.2) * Rder θ V τ' (X1 a) ψ (x * atTau θ V τ (κ k))) +
        (fun k x => (c k * Y k a.1 a.2 * Complex.I) * Rder θ V τ' (X2 a) ψ (x * atTau θ V τ (κ k)))) := by
    funext k
    have hh := isRealPt_atTau hθ τ (hU k)
    have hsm : ψ ∈ SmFun θ V := (h𝒟 ψ hψ).smooth
    rw [show (fun x => c k * ψ (x * atTau θ V τ (κ k))) = c k • rTr V (atTau θ V τ (κ k)) ψ from rfl, Rder_smul,
      Rder_rTr hθ hh hX, GlobalTheory.Size.Rder_eq_sum_glDer hθ hsm (adAt_mem hh hX)]
    funext x
    simp only [Pi.smul_apply, rTr, Finset.sum_apply, smul_eq_mul, GlobalTheory.Size.glDer, RderC, Pi.add_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Y, X1, X2, Z]
    ring
  rw [e]
  have cY : ∀ a : Fin V.rank × Fin V.rank, Continuous fun k => c k * Y k a.1 a.2 := fun a =>
    hc.mul ((continuous_adAt_atTau hθ hκ hU τ' X).matrix_elem a.1 a.2)
  refine Submodule.sum_mem _ fun a _ => add_mem (Submodule.subset_span ⟨_, cY a, _, hR ψ hψ τ' _ ?_, rfl⟩)
    (Submodule.subset_span ⟨_, (cY a).mul continuous_const, _, hR ψ hψ τ' _ ?_, rfl⟩)
  · exact (GlobalTheory.SmoothAutCheck.parts_mem V τ' (Z a)).1
  · exact (GlobalTheory.SmoothAutCheck.parts_mem V τ' (Z a)).2

theorem famSpan_Rder : ∀ F ∈ famSpan θ V τ κ 𝒟, ∀ τ', ∀ X ∈ lieAt V τ',
    (fun k => Rder θ V τ' X (F k)) ∈ famSpan θ V τ κ 𝒟 := by
  intro F hF τ' X hX
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    exact famSpan_Rder_gen hθ hκ hU h𝒟 hR hc hψ τ' hX
  | zero =>
    have e : (fun k => Rder θ V τ' X ((0 : K → GA D V → ℂ) k)) = 0 := by
      funext k g
      simp [Rder]
    rw [e]
    exact zero_mem _
  | add x y hx' hy' hx hy =>
    have sx := famSpan_sm hθ hU h𝒟 x hx'
    have sy := famSpan_sm hθ hU h𝒟 y hy'
    have e : (fun k => Rder θ V τ' X ((x + y) k)) = (fun k => Rder θ V τ' X (x k)) + fun k => Rder θ V τ' X (y k) := by
      funext k
      exact Rder_add (sx k) (sy k) hX
    rw [e]
    exact add_mem hx hy
  | smul a x _ hx =>
    have e : (fun k => Rder θ V τ' X ((a • x) k)) = a • fun k => Rder θ V τ' X (x k) := by
      funext k
      exact Rder_smul a (x k) τ' X
    rw [e]
    exact Submodule.smul_mem _ a hx

end Der

variable (θ V) in

def growN (N : ℕ) : Set (GA D V → ℂ) :=
  {ψ | IsAutFunSm θ V ψ ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    ∀ x, ∃ C, ∀ g ∈ GinfC V, ‖l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ (x * g)‖ ≤ C * normInf θ V g ^ N}

theorem growN_Rder (hθ : IsInfFam θ) (N : ℕ) :
    ∀ ψ ∈ growN θ V N, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ growN θ V N := by
  intro ψ hψ τ' X hX
  refine ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hψ.1, fun l hl x => ?_⟩
  have := hψ.2 (l ++ [(τ', X)]) (fun p hp => ?_) x
  · simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this
  · rcases List.mem_append.1 hp with h | h
    · exact hl p h
    · rw [List.mem_singleton.1 h]; exact hX

theorem famSpan_growth [CompactSpace K] (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (N : ℕ) :
    ∀ F ∈ famSpan θ V τ κ (growN θ V N), ∀ x, ∃ C, ∀ k, ∀ g ∈ GinfC V, ‖F k (x * g)‖ ≤ C * normInf θ V g ^ N := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hF
    intro x
    obtain ⟨C', hC'⟩ := hψ.2 [] (by simp) x
    set Mc := ‖(⟨c, hc⟩ : C(K, ℂ))‖
    set Mh := ‖(⟨_, continuous_normInf_atTau hθ hκ hU⟩ : C(K, ℝ))‖
    refine ⟨Mc * (|C'| * Mh ^ N), fun k g hg => ?_⟩
    have h1 : ‖c k‖ ≤ Mc := ContinuousMap.norm_coe_le_norm (⟨c, hc⟩ : C(K, ℂ)) k
    have h2 : normInf θ V (atTau θ V τ (κ k)) ≤ Mh := by
      have := ContinuousMap.norm_coe_le_norm (⟨_, continuous_normInf_atTau hθ hκ hU⟩ : C(K, ℝ)) k
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, ContinuousMap.coe_mk] using this)
    have h3 := hC' (g * atTau θ V τ (κ k)) (mul_mem hg (atTau_mem (θ := θ) V τ (κ k)))
    simp only [List.foldr_nil] at h3
    have h4 : normInf θ V (g * atTau θ V τ (κ k)) ^ N ≤ (normInf θ V g * Mh) ^ N :=
      pow_le_pow_left₀ (normInf_nonneg _)
        (((GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V).1 _ _).trans (mul_le_mul_of_nonneg_left h2 (normInf_nonneg _))) N
    have h5 : ‖ψ (x * g * atTau θ V τ (κ k))‖ ≤ |C'| * (Mh ^ N * normInf θ V g ^ N) := by
      rw [mul_assoc x]
      refine h3.trans (mul_le_mul (le_abs_self _) ?_ (pow_nonneg (normInf_nonneg _) _) (abs_nonneg _))
      rw [← mul_pow, mul_comm Mh]
      exact h4
    calc ‖c k * ψ (x * g * atTau θ V τ (κ k))‖ = ‖c k‖ * ‖ψ (x * g * atTau θ V τ (κ k))‖ := norm_mul _ _
      _ ≤ Mc * (|C'| * (Mh ^ N * normInf θ V g ^ N)) := mul_le_mul h1 h5 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = Mc * (|C'| * Mh ^ N) * normInf θ V g ^ N := by ring
  | zero => exact fun x => ⟨0, fun k g _ => by simp⟩
  | add F G _ _ hF hG =>
    intro x
    obtain ⟨C1, hC1⟩ := hF x
    obtain ⟨C2, hC2⟩ := hG x
    refine ⟨|C1| + |C2|, fun k g hg => ?_⟩
    have h0 := pow_nonneg (normInf_nonneg (θ := θ) g) N
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add ((hC1 k g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0))
      ((hC2 k g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0)))
  | smul a F _ hF =>
    intro x
    obtain ⟨C, hC⟩ := hF x
    refine ⟨‖a‖ * C, fun k g hg => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC k g hg) (norm_nonneg a)

theorem famSpan_words {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ)
    (hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟) {F : K → GA D V → ℂ}
    (hF : F ∈ famSpan θ V τ κ 𝒟) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    (fun k => l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) ∈ famSpan θ V τ κ 𝒟 := by
  induction l with
  | nil => exact hF
  | cons p l ih =>
    exact famSpan_Rder hθ hκ hU h𝒟 hR _ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) p.1 p.2
      (hl p List.mem_cons_self)

theorem isAutFunSm_RderC (hθ : IsInfFam θ) (τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {ψ : GA D V → ℂ} (h : IsAutFunSm θ V ψ) : IsAutFunSm θ V (RderC θ V τ' Z ψ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
  exact isAutFunSm_add (GlobalTheory.CuspLie.isAutFunSm_Rder hθ h1 h) (isAutFunSm_smul _ (GlobalTheory.CuspLie.isAutFunSm_Rder hθ h2 h))

theorem isAutFunSm_gelf (hθ : IsInfFam θ) (τ' : D.what₂.Tau) (j : ℕ) {ψ : GA D V → ℂ} (h : IsAutFunSm θ V ψ) :
    IsAutFunSm θ V (gelf θ V τ' j ψ) := by
  have key : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, ∀ ψ, IsAutFunSm θ V ψ → IsAutFunSm θ V (f ψ)) →
      IsAutFunSm θ V (l.foldr (fun f acc => f acc) ψ) := by
    intro l hl
    induction l with
    | nil => exact h
    | cons f l ih =>
      exact hl f List.mem_cons_self _ (ih fun g hg => hl g (List.mem_cons_of_mem _ hg))
  unfold gelf
  refine (mem_AFs_iff D θ hθ V _).1 (Submodule.sum_mem _ fun idx _ => (mem_AFs_iff D θ hθ V _).2 (key _ ?_))
  intro f hf
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
  exact fun ψ hψ => isAutFunSm_RderC hθ τ' _ hψ

theorem integrable_avg [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {e : K → ℂ}
    (he : Continuous e) {ψ : GA D V → ℂ} (hψ : Continuous ψ) (x : GA D V) :
    Integrable (fun k => e k * ψ (x * atTau θ V τ (κ k))) μ := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact (he.mul (hψ.comp (continuous_const.mul (continuous_atTau hθ hκ hU)))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem isAutFunSm_average : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ →
    ∀ (V : HSp D) (τ : D.what₂.Tau) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ), Continuous κ →
    (∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∀ e : K → ℂ, Continuous e → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ →
    IsAutFunSm θ V (fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ) := by
  intro D θ hθ V τ K _ _ _ _ μ _ κ hκ hU e he φ hφ
  set 𝒟 : Set (GA D V → ℂ) := {ψ | IsAutFunSm θ V ψ}
  have h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ := fun _ h => h
  have hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟 :=
    fun _ h _ _ hX => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX h
  have FAM := fun ψ (h : IsAutFunSm θ V ψ) => GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V K μ (famSpan θ V τ κ 𝒟)
    (famSpan_cont hθ hκ hU h𝒟) (famSpan_sm hθ hU h𝒟) (famSpan_Rder hθ hκ hU h𝒟 hR)
    (fun k x => e k * ψ (x * atTau θ V τ (κ k))) (Submodule.subset_span ⟨e, he, ψ, h, rfl⟩)
  have F0 := FAM φ hφ
  refine { left := fun γ hγ g => ?_, level := ?_, cont := F0.1, smooth := F0.2.1, zfin := ?_, growth := ?_ }
  · show ∫ k, e k * φ (γ * g * atTau θ V τ (κ k)) ∂μ = ∫ k, e k * φ (g * atTau θ V τ (κ k)) ∂μ
    congr 1
    funext k
    rw [mul_assoc, hφ.left γ hγ]
  · obtain ⟨U, hUo, hk⟩ := hφ.level
    refine ⟨U, hUo, fun u hu hf g => ?_⟩
    show ∫ k, e k * φ (g * u * atTau θ V τ (κ k)) ∂μ = ∫ k, e k * φ (g * atTau θ V τ (κ k)) ∂μ
    congr 1
    funext k
    rw [mul_assoc, ← comm_of_mem V (atTau_mem (θ := θ) V τ (κ k)) hf, ← mul_assoc, hk u hu hf]
  · obtain ⟨W, hWf, hm, hs⟩ := hφ.zfin
    let A : GlobalTheory.Mem.Th.AFs θ V →ₗ[ℂ] (GA D V → ℂ) :=
      { toFun := fun ψ x => ∫ k, e k * ψ.1 (x * atTau θ V τ (κ k)) ∂μ
        map_add' := fun ψ ψ' => by
          funext x
          have c1 := ((mem_AFs_iff D θ hθ V _).1 ψ.2).cont
          have c2 := ((mem_AFs_iff D θ hθ V _).1 ψ'.2).cont
          simp only [Submodule.coe_add, Pi.add_apply, mul_add]
          exact integral_add (integrable_avg μ hθ hκ hU he c1 x) (integrable_avg μ hθ hκ hU he c2 x)
        map_smul' := fun c ψ => by
          funext x
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ c]
          exact integral_const_mul c _ }
    let Wa : Submodule ℂ (GlobalTheory.Mem.Th.AFs θ V) := W.comap (GlobalTheory.Mem.Th.AFs θ V).subtype
    haveI : FiniteDimensional ℂ Wa := Module.Finite.of_injective
      (((GlobalTheory.Mem.Th.AFs θ V).subtype.comp Wa.subtype).codRestrict W fun x => x.2)
      fun a b hab => by
        have h := congrArg (fun z : W => (z : GA D V → ℂ)) hab
        exact Subtype.val_injective (Subtype.val_injective h)
    refine ⟨Wa.map A, Module.Finite.map Wa A,
      Submodule.mem_map.2 ⟨⟨φ, (mem_AFs_iff D θ hθ V φ).2 hφ⟩, hm, rfl⟩, fun τ' j f hf => ?_⟩
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hf
    have hψs := (mem_AFs_iff D θ hθ V _).1 ψ.2
    refine Submodule.mem_map.2 ⟨⟨gelf θ V τ' j ψ.1, (mem_AFs_iff D θ hθ V _).2 (isAutFunSm_gelf hθ τ' j hψs)⟩,
      hs τ' j _ hψ, ?_⟩
    have G := (FAM ψ.1 hψs).2.2.2 τ' j
    show (fun x => ∫ k, e k * gelf θ V τ' j ψ.1 (x * atTau θ V τ (κ k)) ∂μ) =
      gelf θ V τ' j (fun x => ∫ k, e k * ψ.1 (x * atTau θ V τ (κ k)) ∂μ)
    rw [G]
    funext x
    congr 1
    funext k
    have e1 : (fun x => e k * ψ.1 (x * atTau θ V τ (κ k))) = e k • rTr V (atTau θ V τ (κ k)) ψ.1 := rfl
    rw [e1, (linOnSm_gelf τ' j).smul, gelf_rTr hθ (isRealPt_atTau hθ τ (hU k)) τ' j hψs.smooth]
    rfl
  · obtain ⟨N, hN⟩ := hφ.growth
    have h𝒟N : ∀ ψ ∈ growN θ V N, IsAutFunSm θ V ψ := fun _ h => h.1
    have hRN := growN_Rder (V := V) hθ N
    have hF0 : (fun k x => e k * φ (x * atTau θ V τ (κ k))) ∈ famSpan θ V τ κ (growN θ V N) :=
      Submodule.subset_span ⟨e, he, φ, ⟨hφ, hN⟩, rfl⟩
    have FN := GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V K μ (famSpan θ V τ κ (growN θ V N))
      (famSpan_cont hθ hκ hU h𝒟N) (famSpan_sm hθ hU h𝒟N) (famSpan_Rder hθ hκ hU h𝒟N hRN) _ hF0
    refine ⟨N, fun l hl x => ?_⟩
    rw [FN.2.2.1 l hl]
    obtain ⟨C, hC⟩ := famSpan_growth hθ hκ hU N _ (famSpan_words hθ hκ hU h𝒟N hRN hF0 l hl) x
    refine ⟨C * μ.real Set.univ, fun g hg => ?_⟩
    have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall fun k => hC k g hg)
    calc _ ≤ _ := this
      _ = _ := by ring

end GlobalTheory.RealAverage

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ), Continuous κ → (∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∀ e : K → ℂ, Continuous e → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ) := by
  first | exact @GlobalTheory.RealAverage.isAutFunSm_average | exact GlobalTheory.RealAverage.isAutFunSm_average | (intros; apply GlobalTheory.RealAverage.isAutFunSm_average <;> assumption)
end

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactFinite_approxIdentity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ), (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  first | exact @GlobalTheory.KFinApprox.approx_identity | exact GlobalTheory.KFinApprox.approx_identity | (intros; apply GlobalTheory.KFinApprox.approx_identity <;> assumption)
end

section
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.Closed

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem exists_apply_eq (h : Std ε σ) (P : (H → H) → Prop) (a1 : ∀ g ∈ UJset ε, P (σ g))
    (a2 : ∀ T T' : H → H, P T → P T' → P (fun w => T w + T' w) ∧ P (fun w => T (T' w)))
    (a3 : ∀ (c : ℂ) (T : H → H), P T → P (fun w => c • T w))
    (a4 : ∀ e : KG ε → ℂ, KFinFun ε e → P (kAvg ε σ e)) (a5 : P (fun _ => 0))
    {a : H} (ha : a ≠ 0) {v : H} (hv : IsKFin ε σ v) : ∃ T : H → H, P T ∧ T a = v := by
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  let A : Submodule ℂ H :=
    { carrier := {x | ∃ T : H → H, P T ∧ T a = x}
      add_mem' := by
        rintro _ _ ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
        exact ⟨_, (a2 T T' hT hT').1, rfl⟩
      zero_mem' := ⟨_, a5, rfl⟩
      smul_mem' := by
        rintro c _ ⟨T, hT, rfl⟩
        exact ⟨_, a3 c T hT, rfl⟩ }
  have hA : ∀ T : H → H, P T → ∀ x ∈ A, T x ∈ A := by
    rintro T hT _ ⟨T', hT', rfl⟩
    exact ⟨_, (a2 T T' hT hT').2, rfl⟩
  have haA : a ∈ A := ⟨_, a1 1 (one_mem_UJ ε), sigma_one h.1 a⟩
  have hdense : Dense (A : Set H) :=
    dense_of_irred h.2.1 (fun g hg x hx => hA _ (a1 g hg) x hx) ((Submodule.ne_bot_iff _).2 ⟨a, haA, ha⟩)
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → ∀ w, kAvg ε σ e w ∈ A := by
    intro e he w
    have hc : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
    obtain ⟨m, b, c, -, -, -, hbc⟩ := kAvg_finite_rank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (A ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right A F
    have hcl : IsClosed (Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (A : Set H) ⊆ Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact hA _ (a4 e he) x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hdense w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hK⟩ := hv
  haveI : FiniteDimensional ℂ (S ⊓ A : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S A
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ A).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hK⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hK y hyS, hrange _ hk y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

theorem rank_one_mem (h : Std ε σ) (P : (H → H) → Prop) (A1 : ∀ g ∈ UJset ε, P (σ g))
    (A2 : ∀ T T' : H → H, P T → P T' → P (fun w => T w + T' w) ∧ P (fun w => T (T' w)))
    (A3 : ∀ (c : ℂ) (T : H → H), P T → P (fun w => c • T w)) (A5 : P (fun _ => 0))
    {e : KG ε → ℂ} (hQavg : P (kAvg ε σ e)) {m : ℕ} {a c : Fin m → H} (ha : Orthonormal ℂ a)
    (hQ : ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) (k : Fin m) :
    P (fun w => ⟪c k, w⟫_ℂ • ∑ i, ⟪c i, c k⟫_ℂ • a i) := by
  obtain ⟨d, hd⟩ := h.2.2.2.1
  let V : Submodule ℂ (Fin m × Fin m → ℂ) :=
    Submodule.span ℂ ((fun g (p : Fin m × Fin m) => ⟪c p.1, σ g (a p.2)⟫_ℂ) '' UJset ε)
  have hV : ∀ M ∈ V, P (fun w => ∑ i, ∑ j, (M (i, j) * ⟪c j, w⟫_ℂ) • a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      have := (A2 _ _ hQavg (A2 _ _ (A1 g hg) hQavg).2).2
      simp only [hQ, map_sum, map_smul, inner_sum, inner_smul_right, Finset.sum_smul] at this
      simpa only [mul_comm] using this
    | zero => simpa using A5
    | add M N _ _ hM hN =>
      simpa only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib] using (A2 _ _ hM hN).1
    | smul t M _ hM =>
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc] using A3 t _ hM
  have hN : (fun p : Fin m × Fin m => if p.2 = k then ⟪c p.1, c k⟫_ℂ else 0) ∈ V := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have e : ∀ z : Fin m → H, φ (fun p => ⟪c p.1, z p.2⟫_ℂ) =
        ∑ j, ⟪∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i, z j⟫_ℂ := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type, Finset.sum_comm]
      simp [sum_inner, inner_smul_left, mul_comm]
    have hy := eq_zero_of_sum_coef hd ha (y := fun j => ∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i)
      (fun g hg => by rw [← e fun j => σ g (a j)]; exact hφ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    have := e fun j => if j = k then c k else 0
    simp only [hy, inner_zero_left, Finset.sum_const_zero] at this
    refine Eq.trans (congrArg φ ?_) this
    funext p
    by_cases hp : p.2 = k <;> simp [hp]
  have := hV _ hN
  simp only [ite_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  simpa only [Finset.smul_sum, smul_smul, mul_comm] using this

end GlobalTheory.TypeSum.Closed

namespace GlobalTheory.TypeSum

theorem rank_one_mem_of_closed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ Q : (H → H) → Prop, (∀ g ∈ UJset ε, Q (σ g)) → (∀ T T' : H → H, Q T → Q T' → Q (fun w => T w + T' w) ∧ Q (fun w => T (T' w))) → (∀ (c : ℂ) (T : H → H), Q T → Q (fun w => c • T w)) → (∀ e : KG ε → ℂ, KFinFun ε e → Q (kAvg ε σ e)) → Q (fun _ => 0) → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧ ∀ j u, IsKFin ε σ u → Q (fun w => ⟪c j, w⟫_ℂ • u) := by
  intro n ε H _ _ _ σ h Q q1 q2 q3 q4 q5 e he
  obtain ⟨m, a, c, ha, haK, -, hQ⟩ := kAvg_finite_rank n ε H σ h e he
  refine ⟨m, a, c, haK, hQ, fun k u hu => ?_⟩
  obtain ⟨-, -, c3, -⟩ := kCoef_kAvg n ε H σ h.1
  let P : (H → H) → Prop := fun T => Q T ∧ ∀ (z : ℂ) (w : H), T (z • w) = z • T w
  have p1 : ∀ g ∈ UJset ε, P (σ g) := fun g hg => ⟨q1 g hg, fun z w => map_smul (σ g) z w⟩
  have p2 : ∀ T T' : H → H, P T → P T' → P (fun w => T w + T' w) ∧ P (fun w => T (T' w)) :=
    fun T T' hT hT' => ⟨⟨(q2 T T' hT.1 hT'.1).1, fun z w => by simp only [hT.2, hT'.2, smul_add]⟩,
      ⟨(q2 T T' hT.1 hT'.1).2, fun z w => by simp only [hT.2, hT'.2]⟩⟩
  have p3 : ∀ (c : ℂ) (T : H → H), P T → P (fun w => c • T w) :=
    fun c T hT => ⟨q3 c T hT.1, fun z w => by simp only [hT.2, smul_comm c z]⟩
  have p4 : ∀ e : KG ε → ℂ, KFinFun ε e → P (kAvg ε σ e) := by
    intro e he
    refine ⟨q4 e he, fun z w => ?_⟩
    have hc : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
    obtain ⟨L, hL⟩ := c3 e hc
    rw [← hL, ← hL, map_smul]
  have p5 : P (fun _ => 0) := ⟨q5, fun z w => (smul_zero z).symm⟩
  by_cases hk : c k = 0
  · have : (fun w => ⟪c k, w⟫_ℂ • u) = fun _ => 0 := by funext w; simp [hk]
    rw [this]; exact q5
  set b := ∑ i, ⟪c i, c k⟫_ℂ • a i with hb
  have hb0 : b ≠ 0 := by
    intro h0
    apply hk
    have := ha.inner_right_fintype (fun i => ⟪c i, c k⟫_ℂ) k
    rw [← hb, h0, inner_zero_right] at this
    exact inner_self_eq_zero.1 this.symm
  obtain ⟨T, hT, hTb⟩ := Closed.exists_apply_eq h P p1 p2 p3 p4 p5 hb0 hu
  have hR := Closed.rank_one_mem h P p1 p2 p3 p5 (p4 e he) ha hQ k
  have := (p2 T _ hT hR).2.1
  have e' : (fun w => T (⟪c k, w⟫_ℂ • b)) = fun w => ⟪c k, w⟫_ℂ • u := by
    funext w; rw [hT.2, hTb]
  rw [← e']; exact this

end GlobalTheory.TypeSum

end
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ Q : (H → H) → Prop, (∀ g ∈ UJset ε, Q (σ g)) → (∀ T T' : H → H, Q T → Q T' → Q (fun w => T w + T' w) ∧ Q (fun w => T (T' w))) → (∀ (c : ℂ) (T : H → H), Q T → Q (fun w => c • T w)) → (∀ e : KG ε → ℂ, KFinFun ε e → Q (kAvg ε σ e)) → Q (fun _ => 0) → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧ ∀ j u, IsKFin ε σ u → Q (fun w => ⟪c j, w⟫_ℂ • u) := by
  atlas_forward_decl GlobalTheory.TypeSum.rank_one_mem_of_closed
end

section
noncomputable section

namespace GlobalTheory.SeriesToClosure

section Model

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {S : List (List (Mx n))} {v v' : ℕ → H} {ℓ : ℕ → (H →ₗ[ℂ] ℂ)} {C : ℕ → ℝ}
  {f f' : Mx n → ℂ}

theorem sob_add (hσ : IsURepOn (UJset ε) σ) (hS : Words (lieSet ε) S) {x y : H} (hx : Sm ε σ x) (hy : Sm ε σ y) :
    sobNorm σ S (x + y) ≤ sobNorm σ S x + sobNorm σ S y := by
  induction S with
  | nil => simp [sobNorm]
  | cons l S ih =>
    have h1 := ih fun l' h => hS l' (List.mem_cons_of_mem _ h)
    have h2 := norm_add_le (Dw σ l x) (Dw σ l y)
    rw [← Dw_add hσ (hS l List.mem_cons_self) hx hy] at h2
    simp only [sobNorm, List.map_cons, List.sum_cons] at h1 ⊢
    linarith

theorem sob_smul (hσ : IsURepOn (UJset ε) σ) (hS : Words (lieSet ε) S) (c : ℂ) {x : H} (hx : Sm ε σ x) :
    sobNorm σ S (c • x) = ‖c‖ * sobNorm σ S x := by
  induction S with
  | nil => simp [sobNorm]
  | cons l S ih =>
    have h1 := ih fun l' h => hS l' (List.mem_cons_of_mem _ h)
    have h2 := norm_smul c (Dw σ l x)
    rw [← Dw_smul hσ (hS l List.mem_cons_self) c hx] at h2
    simp only [sobNorm, List.map_cons, List.sum_cons] at h1 ⊢
    rw [h1, mul_add]
    exact congrArg (· + _) h2

theorem sob_sum (hσ : IsURepOn (UJset ε) σ) (hS : Words (lieSet ε) S) {ι : Type} (s : Finset ι) (z : ι → ℂ) {a : ι → H}
    (ha : ∀ j, Sm ε σ (a j)) : sobNorm σ S (∑ j ∈ s, z j • a j) ≤ ∑ j ∈ s, ‖z j‖ * sobNorm σ S (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := sob_smul hσ hS 0 (x := 0) (smooth (Jm ε) σ).zero_mem
    simp only [zero_smul, norm_zero, zero_mul] at this
    simp [this]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← sob_smul hσ hS _ (ha j)]
    exact (sob_add hσ hS ((smooth (Jm ε) σ).smul_mem _ (ha j))
      ((smooth (Jm ε) σ).sum_mem fun j _ => (smooth (Jm ε) σ).smul_mem _ (ha j))).trans (by linarith)

abbrev Expn (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) := IsExpnAll (lieSet ε) (UJset ε) σ

theorem Expn.mk' (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) (h1 : ∀ i, Sm ε σ (v' i))
    (h2 : ∀ S', Words (lieSet ε) S' → Summable fun i => C i * sobNorm σ S' (v' i))
    (h3 : ∀ g ∈ UJset ε, HasSum (fun i => ℓ i (σ g (v' i))) (f' g)) : Expn ε σ S v' ℓ C f' :=
  ⟨⟨h1, h.1.2.1, h.1.2.2.1, h2 S hS, h3⟩, h2⟩

theorem Expn.translate (hσ : IsURepOn (UJset ε) σ) (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) {g : Mx n}
    (hg : g ∈ UJset ε) (hf : ∀ y ∈ UJset ε, f' y = f (y * g)) : Expn ε σ S (fun i => σ g (v i)) ℓ C f' := by
  refine h.mk' hS (fun i => Sm.translate hσ (h.1.1 i) hg) (fun S' hS' => ?_) fun y hy => ?_
  · simp only [fun i => sobNorm_translate hσ hg (h.1.1 i) hS']
    refine h.2 _ fun l hl X hX => ?_
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_mem_lie (isUnit_Jm ε) hg (hS' l' hl' Y hY)
  · simp only [← sigma_mul hσ hy hg, hf y hy]
    exact h.1.2.2.2.2 _ (mul_mem_UJ hy hg)

theorem Expn.add (hσ : IsURepOn (UJset ε) σ) (h : Expn ε σ S v ℓ C f) (h' : Expn ε σ S v' ℓ C f')
    (hS : Words (lieSet ε) S) : Expn ε σ S (fun i => v i + v' i) ℓ C fun y => f y + f' y := by
  refine h.mk' hS (fun i => (smooth (Jm ε) σ).add_mem (h.1.1 i) (h'.1.1 i)) (fun S' hS' => ?_) fun y hy => ?_
  · refine Summable.of_nonneg_of_le (fun i => mul_nonneg (h.1.2.1 i) (sobNorm_nonneg _ _ _)) (fun i => ?_)
      ((h.2 S' hS').add (h'.2 S' hS'))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (sob_add hσ hS' (h.1.1 i) (h'.1.1 i)) (h.1.2.1 i)
  · simp only [map_add]
    exact (h.1.2.2.2.2 y hy).add (h'.1.2.2.2.2 y hy)

theorem Expn.smul (hσ : IsURepOn (UJset ε) σ) (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) (c : ℂ) :
    Expn ε σ S (fun i => c • v i) ℓ C fun y => c * f y := by
  refine h.mk' hS (fun i => (smooth (Jm ε) σ).smul_mem c (h.1.1 i)) (fun S' hS' => ?_) fun y hy => ?_
  · simp only [fun i => sob_smul hσ hS' c (h.1.1 i), mul_left_comm _ ‖c‖]
    exact (h.2 S' hS').mul_left _
  · simp only [map_smul, smul_eq_mul]
    exact (h.1.2.2.2.2 y hy).mul_left c

theorem Expn.summable_norm (h : Expn ε σ S v ℓ C f) : Summable fun i => C i * ‖v i‖ := by
  simpa [sobNorm] using h.2 [[]] (by simp [Words])

theorem Expn.term_le (h : Expn ε σ S v ℓ C f) (c : H) {u : H} (hu : Sm ε σ u) (i : ℕ) :
    ‖⟪c, v i⟫_ℂ * ℓ i u‖ ≤ ‖c‖ * (C i * ‖v i‖) * sobNorm σ S u := by
  rw [norm_mul]
  exact (mul_le_mul (norm_inner_le_norm c (v i)) (h.1.2.2.1 i u hu) (norm_nonneg _) (by positivity)).trans
    (le_of_eq (by ring))

theorem Expn.summable_term (h : Expn ε σ S v ℓ C f) (c : H) {u : H} (hu : Sm ε σ u) :
    Summable fun i => ⟪c, v i⟫_ℂ * ℓ i u :=
  Summable.of_norm_bounded ((h.summable_norm.mul_left _).mul_right _) (h.term_le c hu)

theorem Expn.sobFun (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) (c : H) :
    SobFun ε σ fun u => ∑' i, ⟪c, v i⟫_ℂ * ℓ i u := by
  refine ⟨fun x y hx hy => ?_, fun z x _ => ?_, S, ∑' i, ‖c‖ * (C i * ‖v i‖), hS, fun w hw => ?_⟩
  · simp only [map_add, mul_add]
    exact (h.summable_term c hx).tsum_add (h.summable_term c hy)
  · simp only [map_smul, smul_eq_mul, mul_left_comm _ z]
    exact tsum_mul_left
  · exact tsum_of_norm_bounded ((h.summable_norm.mul_left _).hasSum.mul_right _) (h.term_le c hw)

variable [CompleteSpace H]

theorem Expn.avg (hσ : Std ε σ) (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S)
    (hc : Ctrl (lieSet ε) (UJset ε) σ S) {e : KG ε → ℂ} (he : KFinFun ε e) :
    Expn ε σ S (fun i => kAvg ε σ e (v i)) ℓ C fun y => ∫ k, e k * f (y * toMK k) ∂(muK ε) := by
  obtain ⟨m, a, c, -, ha, -, hQ⟩ := kAvg_finite_rank n ε H σ hσ e he
  have ha' := fun j => hσ.2.2.1 _ (ha j)
  have hs : ∀ w, Sm ε σ (kAvg ε σ e w) := fun w => by
    rw [hQ]
    exact (smooth (Jm ε) σ).sum_mem fun j _ => (smooth (Jm ε) σ).smul_mem _ (ha' j)
  refine h.mk' hS (fun i => hs _) (fun S' hS' => ?_)
    ((GlobalTheory.ExpansionAverage.continuousOn_and_hasSum_kAvg n ε H σ hσ S v ℓ C f hS hc h.1).2 e
      (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1) hs)
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (h.1.2.1 i) (sobNorm_nonneg _ _ _)) (fun i => ?_)
    (h.summable_norm.mul_right (∑ j, ‖c j‖ * sobNorm σ S' (a j)))
  rw [mul_assoc, hQ]
  refine mul_le_mul_of_nonneg_left ((sob_sum hσ.1 hS' _ _ ha').trans ?_) (h.1.2.1 i)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => (mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _)
    (sobNorm_nonneg _ _ _)).trans (le_of_eq (by ring))

omit [CompleteSpace H] in
theorem mem_kFin_iff {u : H} : u ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ↔ IsKFin ε σ u := by
  refine ⟨fun h => ?_, fun ⟨W, h1, h2, h3⟩ => (le_sSup (a := W) ⟨h1, h3⟩ : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) h2⟩
  exact (sSup_le fun W hW w hw => ⟨W, hW.1, hw, hW.2⟩ : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ≤ kfin ε σ) h

end Model

section Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.REAL MeasureTheory Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Mx V.rank → (H →L[ℂ] H)) (P : Mx V.rank)

def res (φ : GA D V → ℂ) (x : GA D V) : Mx V.rank → ℂ := fun y => φ (x * atTau θ V τ (P⁻¹ * y * P))

def avg (e : KG ε → ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun x => ∫ k, e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) ∂(muK ε)

def Moves (T : H → H) (φ ψ : GA D V → ℂ) : Prop :=
  ∀ x S v ℓ C, Words (lieSet ε) S → Ctrl (lieSet ε) (UJset ε) σ S → Expn ε σ S v ℓ C (res θ V τ P φ x) →
    Expn ε σ S (fun i => T (v i)) ℓ C (res θ V τ P ψ x)

def Acts (T : H → H) : Prop :=
  ∀ φ, IsAutFunSm θ V φ → ∃ ψ, IsAutFunSm θ V ψ ∧ Moves θ V τ ε σ P T φ ψ

variable {θ V τ ε σ P}

theorem at_mul (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) {a b : Mx V.rank}
    (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    atTau θ V τ (P⁻¹ * (a * b) * P) = atTau θ V τ (P⁻¹ * a * P) * atTau θ V τ (P⁻¹ * b * P) := by
  rw [GrowthAtPlace.conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP hJ ha) (conj_inv_mem hP hJ hb)]

theorem res_conj (hP : IsUnit P) (φ : GA D V → ℂ) (x : GA D V) (g : Mx V.rank) :
    res θ V τ P φ x (P * g * P⁻¹) = φ (x * atTau θ V τ g) := by
  have h : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hP)
  have e : P⁻¹ * (P * g * P⁻¹) * P = g := by
    calc _ = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h, one_mul, mul_one]
  rw [res, e]

theorem res_one (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (φ : GA D V → ℂ) (x : GA D V) :
    res θ V τ P φ x 1 = φ x := by
  rw [res, mul_one, Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hP), atTau_one hθ, mul_one]

theorem continuous_conjK : Continuous fun k : KG ε => P⁻¹ * toMK k * P :=
  (continuous_const.matrix_mul (continuous_toMK ε)).matrix_mul continuous_const

variable [CompleteSpace H]

theorem moves_avg (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) (hσ : Std ε σ)
    {e : KG ε → ℂ} (he : KFinFun ε e) (φ : GA D V → ℂ) :
    Moves θ V τ ε σ P (kAvg ε σ e) φ (avg θ V τ ε P e φ) := by
  intro x S v ℓ C hS hc h
  have h1 := h.avg hσ hS hc he
  refine h1.mk' hS h1.1.1 h1.2 fun y hy => ?_
  have h2 := h1.1.2.2.2.2 y hy
  simp only [res, avg, at_mul hθ hP hJ hy (K_le_UJ (toMK_mem_K _)), ← mul_assoc x] at h2 ⊢
  exact h2

theorem exists_rank_one (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) (hσ : Std ε σ)
    {e : KG ε → ℂ} (he : KFinFun ε e) :
    ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧
      ∀ j u, IsKFin ε σ u → Acts θ V τ ε σ P fun w => ⟪c j, w⟫_ℂ • u := by
  have hsmul : ∀ (c : ℂ) (T : H → H), Acts θ V τ ε σ P T → Acts θ V τ ε σ P fun w => c • T w := fun c T hT φ hφ => by
    obtain ⟨ψ, h1, h2⟩ := hT φ hφ
    exact ⟨c • ψ, isAutFunSm_smul c h1, fun x S v ℓ C hS hc h => (h2 x S v ℓ C hS hc h).smul hσ.1 hS c⟩
  have htr : ∀ g ∈ UJset ε, Acts θ V τ ε σ P (σ g) := fun g hg φ hφ =>
    ⟨_, GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V φ hφ τ _ (conj_inv_mem hP hJ hg),
      fun x S v ℓ C hS _ h => h.translate hσ.1 hS hg fun y hy => by
        simp only [res, rTr, at_mul hθ hP hJ hy hg, mul_assoc x]⟩
  refine GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed _ ε H σ hσ (Acts θ V τ ε σ P) htr (fun T T' hT hT' => ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩) hsmul
    (fun e he φ hφ => ⟨_, GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average D θ hθ V τ (KG ε) (muK ε) _ continuous_conjK
      (fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) e
      (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1) φ hφ, moves_avg hθ hP hJ hσ he φ⟩) ?_ e he
  · obtain ⟨ψ, h1, h2⟩ := hT φ hφ
    obtain ⟨ψ', h1', h2'⟩ := hT' φ hφ
    exact ⟨ψ + ψ', isAutFunSm_add h1 h1', fun x S v ℓ C hS hc h =>
      (h2 x S v ℓ C hS hc h).add hσ.1 (h2' x S v ℓ C hS hc h) hS⟩
  · obtain ⟨ψ', h1', h2'⟩ := hT' φ hφ
    obtain ⟨ψ, h1, h2⟩ := hT ψ' h1'
    exact ⟨ψ, h1, fun x S v ℓ C hS hc h => h2 x S _ ℓ C hS hc (h2' x S v ℓ C hS hc h)⟩
  · simpa using hsmul 0 _ (htr 1 (one_mem_UJ ε))

theorem exists_gkMap (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) (hσ : Std ε σ)
    {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) {S : GA D V → List (List (Mx V.rank))} {v : GA D V → ℕ → H}
    {ℓ : GA D V → ℕ → (H →ₗ[ℂ] ℂ)} {C : GA D V → ℕ → ℝ} (hS : ∀ x, Words (lieSet ε) (S x))
    (hc : ∀ x, Ctrl (lieSet ε) (UJset ε) σ (S x)) (h : ∀ x, Expn ε σ (S x) (v x) (ℓ x) (C x) (res θ V τ P φ x))
    {c : H} (hA : ∀ u, IsKFin ε σ u → Acts θ V τ ε σ P fun w => ⟪c, w⟫_ℂ • u) :
    ∃ T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T ∧
      ∀ u x, T u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u := by
  have hb := fun x => (h x).sobFun (hS x) c
  have hsm : ∀ u : kFin ε σ, Sm ε σ u := fun u => hσ.2.2.1 _ (mem_kFin_iff.1 u.2)
  let T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun u x => ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u
      map_add' := fun a b => funext fun x => (hb x).1 _ _ (hsm a) (hsm b)
      map_smul' := fun z a => funext fun x => (hb x).2.1 z _ (hsm a) }
  have key : ∀ u : kFin ε σ, IsAutFunSm θ V (T u) ∧
      ∀ x, ∀ y ∈ UJset ε, res θ V τ P (T u) x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (σ y u) := fun u => by
    obtain ⟨ψ, h1, h2⟩ := hA u (mem_kFin_iff.1 u.2) φ hφ
    have h3 : ∀ x, ∀ y ∈ UJset ε, res θ V τ P ψ x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (σ y u) := fun x y hy => by
      have := (h2 x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 y hy
      simp only [map_smul, smul_eq_mul] at this
      exact this.tsum_eq.symm
    have e : T u = ψ := funext fun x => by
      have := h3 x 1 (one_mem_UJ ε)
      rw [res_one hθ hP, sigma_one hσ.1] at this
      exact this.symm
    rw [e]
    exact ⟨h1, h3⟩
  refine ⟨T, ⟨fun u => (key u).1, fun g _ hg a b hab => funext fun x => ?_, fun X hX a b hab => funext fun x => ?_⟩,
    fun _ _ => rfl⟩
  · rw [rTr, ← res_conj hP (T a) x g, (key a).2 x _ (K_le_UJ hg), ← hab]
    rfl
  · have hd := (isUnit_iff_isUnit_det _).1 hP
    have hY : P * X * P⁻¹ ∈ lieSet ε := by
      refine Transport.conj_lie (G := gramAt D V τ) (Matrix.nonsing_inv_mul _ hd) ?_ hX
      rw [← hJ]
      calc _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
    simp only [← Transport.exp_smul_conj hP] at hab
    have e : (b : H) = dRep σ (P * X * P⁻¹) a := hab.deriv.symm
    have h1 := (hσ.hasDerivAt_sobFun (hb x) (hsm a) hY).deriv
    rw [← e] at h1
    refine h1.symm.trans ?_
    unfold Rder oneP
    congr 1
    funext t
    rw [← res_conj hP (T a) x, ← Transport.exp_smul_conj hP, (key a).2 x _ (exp_mem_UJ hY t)]

end Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.REAL MeasureTheory GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes in
open scoped InnerProductSpace in

theorem hasTypeAt_of_isTypeAt : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ),
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CasselmanWallach → IsInfFam (D := D) θ → V.SigOK →
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsAutFunSm θ V φ →
    IsTypeAt θ V τ S φ → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ := by
  intro D θ V τ S φ _ _ hHC _ hθ _ hS hφ ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hJ, hx⟩ K hK δ hδ
  haveI : CompleteSpace H := hD.1
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hσ : Std ε σ := std_of_isDS hHC hD
  have hlam : Formalism.QuantumDeterminants.IsHCParam lam := by
    obtain ⟨l, e, h1, h2, -⟩ := hS
    rwa [(GlobalTheory.SignedParTest.isEnum_unique hE h1).1]
  have hx' : ∀ x, HasTypeAll (lieSet ε) (UJset ε) σ (res θ V τ P φ x) := fun x =>
    hasTypeAll_transport _ H H _ σ (gramAt D V τ) (Jm ε) P (isUnit_gram hP hJ) hP hJ (LinearIsometryEquiv.refl ℂ H)
      (fun _ _ _ => rfl) (fun g => φ (x * atTau θ V τ g)) (hasTypeAll_iff.2 (hx x))
  choose W hW hc v ℓ C h using hx'
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  obtain ⟨e, he, hap⟩ := GlobalTheory.T.exists_compactFinite_approxIdentity _ ε (GA D V) (fun x k => φ (x * atTau θ V τ (P⁻¹ * toMK k * P)))
    (hφ.cont.comp (continuous_fst.mul (hk.comp continuous_snd))) K hK δ hδ
  obtain ⟨m, a, c, ha, hQ, hA⟩ := exists_rank_one hθ hP hJ hσ he
  choose T hT hTv using fun j => exists_gkMap hθ hP hJ hσ hφ hW hc h (hA j)
  refine ⟨∑ j, T j ⟨a j, mem_kFin_iff.2 (ha j)⟩, Submodule.sum_mem _ fun j _ =>
    (le_sSup (a := LinearMap.range (T j)) ⟨H, _, _, σ, lam, ε, P, T j, hE, hlam, hD, hP, hJ, hT j, rfl⟩ :
      _ ≤ finPartOfType θ V τ S) ⟨_, rfl⟩, fun x hxK => ?_⟩
  have h1 := (moves_avg hθ hP hJ hσ he φ x _ _ _ _ (hW x) (hc x) (h x)).1.2.2.2.2 1 (one_mem_UJ ε)
  simp only [res_one hθ hP, sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
  have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (ha j))).hasSum)
  have h3 := hap x hxK
  have h4 : φ (x * atTau θ V τ (P⁻¹ * toMK (1 : KG ε) * P)) = φ x := res_one hθ hP φ x
  simp only [Finset.sum_apply, hTv]
  rw [← h2, ← h4]
  exact h3

end GlobalTheory.SeriesToClosure

end
end
