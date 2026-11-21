import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicOpenNeighbourhoodProduct
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspDiscreteDecompositionOfDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.WeilBound.CoreStatements.MeasureExistence.ExistsMeas
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrbit

section
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Glob

theorem finiteDimensional_of_compact_coercive :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c →
        (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  intro H _ _ _ A hA S c hc hS
  have hS' : ∀ u ∈ S.topologicalClosure, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
    intro u hu
    have hcl : IsClosed {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} :=
      isClosed_le (continuous_const.mul (continuous_norm.pow 2))
        (Complex.continuous_re.comp (continuous_id.inner A.continuous))
    have hsub : (S : Set H) ⊆ {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} := fun u hu ↦ hS u hu
    have h := closure_minimal hsub hcl
    rw [← Submodule.topologicalClosure_coe] at h
    exact h hu
  have hbd : ∀ u ∈ S.topologicalClosure, ‖u‖ ≤ c⁻¹ * ‖A u‖ := by
    intro u hu
    have h1 := hS' u hu
    have h2 : (⟪u, A u⟫_ℂ).re ≤ ‖u‖ * ‖A u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h3 : c * ‖u‖ ≤ ‖A u‖ := by
      rcases (norm_nonneg u).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        exact norm_nonneg _
      · nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  let T : S.topologicalClosure →L[ℂ] H := A.comp S.topologicalClosure.subtypeL
  have hT : IsCompactOperator T := hA.comp_clm S.topologicalClosure.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    refine ContinuousLinearMap.antilipschitz_of_bound T fun x ↦ ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    exact hbd x x.2
  have hemb : Topology.IsClosedEmbedding T := hanti.isClosedEmbedding T.uniformContinuous
  have hK := IsCompactOperator.isCompact_closure_image_closedBall
    (f := (T : S.topologicalClosure →ₗ[ℂ] H)) hT 1
  have hball : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  have : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hball
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure

end GlobalTheory.CompanionTheory.Glob
end

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c → (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspFin

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil

theorem le_re_inner_of_isRepOp {G H : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : G →* (H →L[ℂ] H)} {μ : Measure G} {φ : G → ℝ} {T : H →L[ℂ] H}
    (hT : IsRepOp π μ (fun g => (φ g : ℂ)) T) (hφ : Integrable φ μ) (h0 : 0 ≤ φ) {N : Set G}
    (hs : Function.support φ ⊆ N) (u : H) (c : ℝ) (hc : ∀ g ∈ N, c ≤ (⟪u, π g u⟫_ℂ).re) :
    c * ∫ g, φ g ∂μ ≤ (⟪u, T u⟫_ℂ).re := by
  have hi := (hT u).1
  have hin : Integrable (fun g => ⟪u, (φ g : ℂ) • π g u⟫_ℂ) μ := hi.const_inner u
  have e : (⟪u, T u⟫_ℂ).re = ∫ g, (⟪u, (φ g : ℂ) • π g u⟫_ℂ).re ∂μ := by
    rw [(hT u).2, ← integral_inner hi u]
    exact (integral_re hin).symm
  rw [e, ← integral_const_mul]
  refine integral_mono (hφ.const_mul c) hin.re fun g => ?_
  simp only [inner_smul_right, Complex.re_ofReal_mul]
  by_cases hg : φ g = 0
  · simp [hg]
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hc g (hs hg)) (h0 g)

variable {D : D7} {V : HSp D}

theorem exists_bump (μ : Measure (GA D V)) [μ.IsHaarMeasure] {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V)) :
    ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ Function.support φ ⊆ N ∧ Integrable φ μ ∧
      0 < ∫ g, φ g ∂μ := by
  obtain ⟨φ, hφ, h0, h1, hs⟩ : ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ φ 1 = 1 ∧
      Function.support φ ⊆ N := GlobalTheory.CuspSpectrum.exists_bump_ccAd (isCMExt_host D) hN
  have hc := continuous_of_mem_ccAd hφ
  have hφc : Continuous φ := Complex.continuous_re.comp hc.1
  have hφs : HasCompactSupport φ := hc.2.comp_left (g := Complex.re) rfl
  exact ⟨φ, hφ, h0, hs, hφc.integrable_of_hasCompactSupport hφs,
    hφc.integral_pos_of_hasCompactSupport_nonneg_nonzero hφs h0 (x := 1) (by rw [h1]; exact one_ne_zero)⟩

theorem finiteDimensional_of_coercive (hP : GlobalTheory.Published.CuspDecayBound) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Sb : Submodule ℂ (L2cusp V μ)) {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V))
    (h : ∀ g ∈ N, ∀ u ∈ Sb, (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ (⟪u, Rcusp V μ g u⟫_ℂ).re) : FiniteDimensional ℂ Sb := by
  obtain ⟨φ, hf, h0, hs, hi, hpos⟩ := exists_bump μ hN
  have hrep := GlobalTheory.CuspSpectrum.isRepOp_RcuspOp (μ := μ) hf
  refine GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive (L2cusp V μ) (RcuspOp V μ _)
    (isCompactOperator_of_isHilbertSchmidt (GlobalTheory.CuspHS.isHilbertSchmidt_RcuspOp hP hf)) Sb
    ((1 / 2) * ∫ g, φ g ∂μ) (by positivity) fun u hu => ?_
  have := le_re_inner_of_isRepOp hrep hi h0 hs u ((1 / 2 : ℝ) * ‖u‖ ^ 2) fun g hg => h g hg u hu
  calc _ = (1 / 2 : ℝ) * ‖u‖ ^ 2 * ∫ g, φ g ∂μ := by ring
    _ ≤ _ := this

end GlobalTheory.CompanionTheory.CuspFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

variable (θ V) in

abbrev Mc : Submodule ℂ (GA D V → ℂ) := cuspForms θ V ⊥

theorem mem_Mc_iff {φ : GA D V → ℂ} : φ ∈ Mc θ V ↔ IsAutFunSm θ V φ ∧ IsCuspFun V φ := by
  refine ⟨fun h => (mem_cuspForms.1 h).1, fun h => mem_cuspForms.2 ⟨h, ?_⟩⟩
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨Submodule.span ℂ {φ}, inferInstance, fun k hk => ?_⟩
  rw [Subgroup.mem_bot.1 hk]
  exact Submodule.subset_span (by simp [funext_iff])

def der (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Module.End ℂ (Mc θ V) where
  toFun φ := ⟨Rder θ V τ X φ.1, mem_Mc_iff.2
    ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX (mem_Mc_iff.1 φ.2).1,
      GlobalTheory.CuspLie.isCuspFun_Rder hθ hX (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩⟩
  map_add' f g := Subtype.ext (Rder_add (mem_Mc_iff.1 f.2).1.smooth (mem_Mc_iff.1 g.2).1.smooth hX)
  map_smul' c f := Subtype.ext (Rder_smul c f.1 τ X)

@[simp] theorem der_coe (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : Mc θ V) : (der hθ τ hX φ : GA D V → ℂ) = Rder θ V τ X φ.1 := rfl

def io (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) : Mc θ V →ₗ[ℂ] L2cusp V μ :=
  cuspToL2 ⊥ μ (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ

theorem io_injective (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) :
    Function.Injective (io (V := V) μ hθ) := cusp_form_toL2_injective _ hθ

def derInf (hθ : IsInfFam θ) (X : GlobalTheory.SmoothForms.LieN V) : Module.End ℂ (Mc θ V) :=
  ∑ τ, der hθ τ (X := (X τ).1) (X τ).2

def IsKLie {n : ℕ} (e : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  yᴴ = -y ∧ y * Formalism.REAL.Jm e = Formalism.REAL.Jm e * y

end GlobalTheory.CompanionTheory.HCCusp
end
end
