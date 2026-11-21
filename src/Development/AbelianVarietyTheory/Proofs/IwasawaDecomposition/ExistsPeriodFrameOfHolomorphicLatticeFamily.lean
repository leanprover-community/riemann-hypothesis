import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalSymplecticBasisAdaptedCoisotropic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem latBasis_logCover_real_holo : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  intro n a g r K lam hK hlam hB

  have hne : (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0) ∈ logDom n a := by
    intro k
    by_cases h : (k : ℕ) < a <;> simp [h]
  obtain ⟨hOpen, -, hAn, hMaps⟩ := GlobalTheory.logDom_chart_props n a

  have hmem : ∀ s ∈ logDom n a, ∀ j, lam s j ∈ K (logExp a s) := by
    intro s hs j
    refine ((hB s hs).2.2 _).2 ⟨Pi.single j 1, ?_⟩
    simp [Pi.single_apply]
  have hreal : ∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) := by
    intro s hs
    obtain ⟨hli, hsp, hK'⟩ := hB s hs
    have hspanK : Submodule.span ℝ (K (logExp a s)) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hmem s hs j)
    exact (GlobalTheory.LatReal.isRealBasis_of_isLatFam n g r (Metric.ball 0 1) K (logExp a s) (lam s) hK
      (hMaps hs) hspanK hli hK').1
  refine ⟨?_, hreal, ?_⟩
  · set s₀ := (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0)
    have hli := hreal s₀ hne
    have hsp := (hB s₀ hne).2.1
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hli
    rw [Set.finrank, hsp, finrank_top, Fintype.card_fin] at h1
    rw [h1, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  · intro j k
    have hF := IsLatFam.pullback_analytic n n g (Metric.ball 0 1) (logDom n a) K (logExp a) hK hOpen
      (fun s _ => hAn s) hMaps
    intro s₀ hs₀
    have hnhds : logDom n a ∈ 𝓝 s₀ := hOpen.mem_nhds hs₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := hF.2.2.2 s₀ hs₀ (lam s₀ j) (hmem s₀ hs₀ j)
    have hc : ContinuousAt (fun s => (s, lam s j)) s₀ :=
      continuousAt_id.prodMk ((continuous_apply j).continuousAt.comp (hlam.continuousAt hnhds))
    have hev' : ∀ᶠ s in 𝓝 s₀, (lam s j ∈ K (logExp a s) ↔ lam s j = ζ s) := by
      have := hc.tendsto.eventually hev
      simpa [hζ0] using this
    have heq : (fun s => lam s j) =ᶠ[𝓝 s₀] ζ := by
      filter_upwards [hev', hnhds] with s h1 h2
      exact h1.1 (hmem s h2 j)
    have hd : DifferentiableAt ℂ (fun s => lam s j) s₀ :=
      hζa.differentiableAt.congr_of_eventuallyEq heq
    exact (differentiableAt_pi.1 hd k).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.punctPolydiscCover_latticeBasis_real_holomorphic : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_eq_of_im_eq_on_span : ∀ (g r : ℕ) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ), Submodule.span ℝ (Set.range l) = ⊤ → (∀ i j, (hermForm Hm (l i) (l j)).im = (hermForm Hm' (l i) (l j)).im) → Hm = Hm' := by
  intro g r Hm Hm' l hspan h
  have h1 : ∀ z, ∀ j, (hermForm Hm z (l j)).im = (hermForm Hm' z (l j)).im := by
    intro z j
    have hz : z ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h i j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm Hm z w).im = (hermForm Hm' z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact h1 z j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexMatrix_eq_of_hermForm_im_eq_real_span : ∀ (g r : ℕ) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ), Submodule.span ℝ (Set.range l) = ⊤ → (∀ i j, (hermForm Hm (l i) (l j)).im = (hermForm Hm' (l i) (l j)).im) → Hm = Hm' := by
  atlas_forward_decl GlobalTheory.hermForm_eq_of_im_eq_on_span
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_swap_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_sum, star_mul', Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h, star_star]
  ring

theorem hermForm_im_antisymm : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian →
    (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := by
  intro g r Hm l M hH hM
  ext i j
  have h1 := hM j i
  rw [hermForm_swap_of_isHermitian Hm hH] at h1
  have h2 := hM i j
  simp only [Complex.star_def, Complex.conj_im] at h1
  have : ((M j i : ℤ) : ℝ) = ((-M i j : ℤ) : ℝ) := by push_cast; linarith
  simpa [Matrix.transpose_apply] using Int.cast_injective this

example : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := hermForm_im_antisymm

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_intMatrix_transpose_neg : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := by
  atlas_forward_decl GlobalTheory.hermForm_im_antisymm
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem hermForm_im_intComb : ∀ (g r r' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r' → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ i j, (hermForm Hm (w i) (w j)).im = ((c * M * cᵀ) i j : ℝ) := by
  intro g r r' Hm l w c M hw hM i j
  rw [hw i, hw j, hermForm_im_sum]
  simp only [hM]
  push_cast [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_intCombination_eq_conj_mul : ∀ (g r r' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r' → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ i j, (hermForm Hm (w i) (w j)).im = ((c * M * cᵀ) i j : ℝ) := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem hermForm_im_intComb_dotProduct : ∀ (g r r₀ : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ u u' : Fin r₀ → ℤ, (hermForm Hm (∑ i, u i • w i) (∑ j, u' j • w j)).im = (((∑ i, u i • c i) ⬝ᵥ M *ᵥ (∑ i, u' i • c i) : ℤ) : ℝ) := by
  intro g r r₀ Hm l w c M hw hM u u'
  have hre : ∀ v : Fin r₀ → ℤ, ∑ i, v i • w i = ∑ j, (∑ i, v i • c i) j • l j := by
    intro v
    simp only [hw, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hre u, hre u', hermForm_im_sum]
  simp only [hM, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_intCombination_dotProduct : ∀ (g r r₀ : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ u u' : Fin r₀ → ℤ, (hermForm Hm (∑ i, u i • w i) (∑ j, u' j • w j)).im = (((∑ i, u i • c i) ⬝ᵥ M *ᵥ (∑ i, u' i • c i) : ℤ) : ℝ) := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameFix

theorem coeff_mul_eq_of_same_combinations :
    ∀ (g r r₀ : ℕ) (l l' : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ)
      (T : Matrix (Fin r) (Fin r) ℤ), LinearIndependent ℤ l → (∀ i, l' i = ∑ j, T i j • l j) →
      (∀ i, w i = ∑ j, c i j • l j) → (∀ i, w i = ∑ j, c i j • l' j) → c * T = c := by
  intro g r r₀ l l' w c T hl hl' h1 h2
  ext i m
  have key : ∑ j, c i j • l' j = ∑ m, (c * T) i m • l m := by
    simp only [hl', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have hsum : ∑ m, ((c * T) i m - c i m) • l m = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← key, ← h2, h1, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hl (fun m => (c * T) i m - c i m) hsum m)

end GlobalTheory.FrameFix
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffMatrix_mul_eq_of_same_intCombinations : ∀ (g r r₀ : ℕ) (l l' : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (T : Matrix (Fin r) (Fin r) ℤ), LinearIndependent ℤ l → (∀ i, l' i = ∑ j, T i j • l j) → (∀ i, w i = ∑ j, c i j • l j) → (∀ i, w i = ∑ j, c i j • l' j) → c * T = c := by
  atlas_forward_decl GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem symplecticPair_decomp {g r : ℕ} (hr : r = 2 * g) (M' : Matrix (Fin r) (Fin r) ℚ)
    (hM : M'ᵀ = -M') (ε φ : Matrix (Fin g) (Fin r) ℚ) (h1 : ε * M' * εᵀ = 0)
    (h2 : φ * M' * φᵀ = 0) (h3 : φ * M' * εᵀ = 1) (X : Matrix (Fin g) (Fin r) ℚ) :
    X = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
  have h4 : ε * M' * φᵀ = -1 := by
    have := congrArg Matrix.transpose h3
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM,
      Matrix.transpose_one] at this
    rw [← neg_neg (ε * M' * φᵀ), ← this]
    simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  have hPR : Matrix.fromRows ε φ * (M' * Matrix.fromCols (-φᵀ) εᵀ) = 1 := by
    rw [Matrix.mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_neg,
      h1, h2, h3, h4, neg_neg, neg_zero, Matrix.fromBlocks_one]
  let e : Fin g ⊕ Fin g ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  have hRP : (M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).mp hPR
  calc X = X * ((M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ) := by
        rw [hRP, Matrix.mul_one]
    _ = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
        rw [Matrix.mul_assoc M', Matrix.fromCols_mul_fromRows]
        simp only [Matrix.mul_add, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]

theorem isometry_fixing_rowSpace_shift : ∀ (g r r₀ rk : ℕ) (M T : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ), r = 2 * g → Mᵀ = -M → T * M * Tᵀ = M → c * T = c → (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) → ∃ b : Matrix (Fin g) (Fin g) ℚ, (∀ i j : Fin g, (rk ≤ i.val ∨ rk ≤ j.val) → b i j = 0) ∧ φ * T.map (Int.cast : ℤ → ℚ) = φ + bᵀ * (α * c.map (Int.cast : ℤ → ℚ)) := by
  intro g r r₀ rk M T c α φ β hr hMt hTM hcT hεε hφφ hφε hβ
  have keyZ : T * M * cᵀ = M * cᵀ := by
    calc T * M * cᵀ = T * M * (c * T)ᵀ := by rw [hcT]
      _ = T * M * Tᵀ * cᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc (T * M)]
      _ = M * cᵀ := by rw [hTM]
  have hcTZ : c * T = c := hcT
  have map_mul' : ∀ {a b d : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) (B : Matrix (Fin b) (Fin d) ℤ),
      (A * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ) :=
    fun A B => Matrix.map_mul (f := Int.castRingHom ℚ)
  set M' := M.map (Int.cast : ℤ → ℚ) with hM'
  set T' := T.map (Int.cast : ℤ → ℚ) with hT'
  set c' := c.map (Int.cast : ℤ → ℚ) with hc'
  have key : T' * M' * c'ᵀ = M' * c'ᵀ := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) keyZ
    simpa only [map_mul', Matrix.transpose_map] using this
  have hcT' : c' * T' = c' := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) hcTZ
    simpa only [map_mul'] using this
  have hMt' : M'ᵀ = -M' := by
    rw [hM', ← Matrix.transpose_map, hMt]; ext i j; simp
  set ε := α * c' with hε
  set X := φ * T' - φ with hX
  have hXc : X * M' * c'ᵀ = 0 := by
    rw [hX, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc φ T', Matrix.mul_assoc φ (T' * M'),
      key, Matrix.mul_assoc φ M', sub_self]
  have hXε : X * M' * εᵀ = 0 := by
    rw [hε, Matrix.transpose_mul, ← Matrix.mul_assoc, hXc, Matrix.zero_mul]
  have hdec := symplecticPair_decomp hr M' hMt' ε φ hεε hφφ hφε X
  rw [hXε, Matrix.zero_mul, add_zero] at hdec
  refine ⟨-(X * M' * φᵀ)ᵀ, ?_, ?_⟩
  · intro i j hij
    simp only [Matrix.neg_apply, Matrix.transpose_apply, neg_eq_zero]
    rcases hij with hi | hj
    ·
      have : (X * M' * φᵀ) j i = (X * M' * c'ᵀ * βᵀ) j i := by
        rw [Matrix.mul_assoc (X * M') c'ᵀ, ← Matrix.transpose_mul]
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hβ i hi m]
        simp only [Matrix.mul_apply]
      rw [this, hXc, Matrix.zero_mul, Matrix.zero_apply]
    · have hrow : ∀ m, X j m = 0 := by
        intro m
        have hφj : ∀ m, φ j m = (β * c') j m := hβ j hj
        rw [hX, Matrix.sub_apply, Matrix.mul_apply, hφj m]
        have : ∑ k, φ j k * T' k m = ((β * c') * T') j m := by
          simp only [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hφj k]; simp only [Matrix.mul_apply]
        rw [this, Matrix.mul_assoc, hcT', sub_self]
      simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]
  · rw [Matrix.transpose_neg, Matrix.transpose_transpose, ← hdec, hX]
    abel

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intIsometry_fixing_rowSpace_symplectic_shift : ∀ (g r r₀ rk : ℕ) (M T : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ), r = 2 * g → Mᵀ = -M → T * M * Tᵀ = M → c * T = c → (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) → ∃ b : Matrix (Fin g) (Fin g) ℚ, (∀ i j : Fin g, (rk ≤ i.val ∨ rk ≤ j.val) → b i j = 0) ∧ φ * T.map (Int.cast : ℤ → ℚ) = φ + bᵀ * (α * c.map (Int.cast : ℤ → ℚ)) := by
  atlas_forward_decl GlobalTheory.isometry_fixing_rowSpace_shift
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rat_matrix_common_denom : ∀ (a g : ℕ) (b : Fin a → Matrix (Fin g) (Fin g) ℚ), ∃ (D : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D ∧ ∀ k i j, (B k i j : ℚ) = D * b k i j := by
  intro a g b
  classical
  let D : ℕ := ∏ k, ∏ i, ∏ j, (b k i j).den
  have hdvd : ∀ k i j, (b k i j).den ∣ D := fun k i j =>
    dvd_trans (Finset.dvd_prod_of_mem (fun j => (b k i j).den) (Finset.mem_univ j))
      (dvd_trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (b k i j).den) (Finset.mem_univ i))
        (Finset.dvd_prod_of_mem (fun k => ∏ i, ∏ j, (b k i j).den) (Finset.mem_univ k)))
  refine ⟨D, fun k i j => ((D / (b k i j).den : ℕ) : ℤ) * (b k i j).num, ?_, ?_⟩
  · exact Finset.prod_pos fun k _ => Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (b k i j).den_pos
  · intro k i j
    obtain ⟨m, hm⟩ := hdvd k i j
    have hD : D = (b k i j).den * m := hm
    simp only
    rw [hD, Nat.mul_div_cancel_left _ (b k i j).den_pos]
    push_cast
    rw [mul_comm ((b k i j).den : ℚ) (m : ℚ), _root_.mul_assoc, Rat.den_mul_eq_num]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_rat_matrices : ∀ (a g : ℕ) (b : Fin a → Matrix (Fin g) (Fin g) ℚ), ∃ (D : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D ∧ ∀ k i j, (B k i j : ℚ) = D * b k i j := by
  atlas_forward_decl GlobalTheory.rat_matrix_common_denom
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodFrame

theorem frame_hermForm_sum_left {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
  unfold hermForm
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]

theorem frame_hermForm_sum_right {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
  have hs : star (∑ i, c i • E i) = ∑ i, star (c i) • star (E i) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext k
    simp [mul_comm]
  simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_col {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) (i : Fin g) :
    (fun k => combMat l ε k i) = ∑ m, (ε i m : ℂ) • l m := by
  funext k
  simp [combMat, Finset.sum_apply]

theorem frame_im_hermForm {g r : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ)
    (l : Fin r → Fin g → ℂ) (hM : ∀ i j, (hermForm Hm (l i) (l j)).im = M i j)
    (A B : Matrix (Fin g) (Fin r) ℚ) (i k : Fin g) :
    (hermForm Hm (fun x => combMat l A x i) (fun x => combMat l B x k)).im
      = (((A * M.map (Int.cast : ℤ → ℚ) * Bᵀ) i k : ℚ) : ℝ) := by
  rw [frame_col, frame_col, frame_hermForm_sum_left]
  simp only [frame_hermForm_sum_right, Finset.mul_sum, Complex.im_sum]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  push_cast
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.mul_im, hM]
  ring

theorem riemann_relations_frame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  intro g r Hm M l ε φ D hD hH hpos _hl hM hεε hφφ hφε
  set P := combMat l ε with hP
  set Q := combMat l φ with hQ
  set E : Fin g → Fin g → ℂ := fun i k => P k i with hE
  set F : Fin g → Fin g → ℂ := fun j k => Q k j with hF
  have hEE : ∀ i j, (hermForm Hm (E i) (E j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM ε ε i j
    rw [hεε] at h
    simpa using h
  have hFF : ∀ i j, (hermForm Hm (F i) (F j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ φ i j
    rw [hφφ] at h
    simpa using h
  have hFE : ∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ ε i j
    rw [hφε] at h
    change (hermForm Hm (F i) (E j)).im = _ at h
    rw [h]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hind : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : hermForm Hm (F j) (∑ i, ((a i : ℝ) : ℂ) • E i) = 0 := by
      have hs : (∑ i, ((a i : ℝ) : ℂ) • E i) = ∑ i, a i • E i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ext k
        simp
      rw [hs, ha]
      simp [hermForm]
    rw [frame_hermForm_sum_right] at h1
    have h2 := congrArg Complex.im h1
    simpa [Complex.im_sum, Complex.mul_im, hFE] using h2
  have hdet : P.det ≠ 0 := by
    have h := GlobalTheory.det_ne_zero_of_real_indep_isotropic g Hm E hpos hind hEE
    exact h
  have hU : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := P⁻¹ * Q with hτ
  have hPτ : P * τ = Q := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hFτ : ∀ j, F j = ∑ i, τ i j • E i := by
    intro j
    funext k
    have h := congrFun (congrFun hPτ k) j
    simp only [Matrix.mul_apply] at h
    simp only [hF, hE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨hposτ, hsymτ⟩ := GlobalTheory.riemann_relations_period_matrix g g Hm E F τ hH hpos hFτ hEE hFE
  have hτs : ∀ i j, τ i j = τ j i := fun i j => by
    have h := hsymτ i j
    rw [hFF] at h
    simpa [sub_eq_zero] using h
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hY
  set a : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hEE])
  have hYA : Y * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hFτ j, frame_hermForm_sum_left] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, zero_add] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hY, Matrix.map_apply]
    rw [hτs j i]
  have hTim : ((D : ℂ) • τ).map Complex.im = (D : ℝ) • Y := by
    ext i j
    simp [hY]
  have hTre : (((D : ℂ) • τ).map Complex.im).map Complex.ofReal = (D : ℂ) • Y.map Complex.ofReal := by
    rw [hTim]
    ext i j
    simp
  have hYAc : Y.map Complex.ofReal * a.map Complex.ofReal = 1 := by
    ext i k
    have h := congrFun (congrFun hYA i) k
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hinv : ((((D : ℂ) • τ).map Complex.im).map Complex.ofReal)⁻¹ = (D : ℂ)⁻¹ • a.map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [hTre, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hDne, one_smul, hYAc]
  refine ⟨hU, ?_, ?_, ?_⟩
  · show ((D : ℂ) • τ)ᵀ = (D : ℂ) • τ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply]
    rw [hτs j i]
  · rw [Matrix.posDef_iff_dotProduct_mulVec, hTim]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial, hY, Matrix.map_apply]
      rw [hτs j i]
    · have e : star x ⬝ᵥ (((D : ℝ) • Y) *ᵥ x) = (D : ℝ) * (∑ i, ∑ j, (x i : ℂ) * τ i j * (x j : ℂ)).im := by
        simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Complex.im_sum,
          Finset.mul_sum, hY, Matrix.map_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [Complex.mul_im]
        ring
      rw [e]
      exact mul_pos (by exact_mod_cast hD) (hposτ x hx)
  · rw [hinv, smul_smul, Complex.ofReal_natCast, mul_inv_cancel₀ hDne, one_smul]
    ext i j
    rw [Matrix.map_apply, ← hAr i j]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, Pi.star_apply, Matrix.map_apply, hE, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring

end GlobalTheory.PeriodFrame
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannRelations_rationalCombinationFrame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  atlas_forward_decl GlobalTheory.PeriodFrame.riemann_relations_frame
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

private theorem differentiableOn_finsetProd' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Idx : Type}
    (u : Finset Idx) (f : Idx → E → ℂ) {S : Set E} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun s => ∏ i ∈ u, f i s) S := by
  classical
  revert h
  refine Finset.induction_on u ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact differentiableOn_const _
  · intro a u ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).fun_mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableOn_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S) :
    DifferentiableOn ℂ (fun s => (M s).det) S := by
  have hdet : (fun s => (M s).det) = fun s => ∑ σ : Equiv.Perm (Fin g),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i := by
    funext s
    exact Matrix.det_apply' (M s)
  rw [hdet]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  exact differentiableOn_finsetProd' Finset.univ (fun i s => M s (σ i) i) (fun i _ => h (σ i) i)

theorem differentiableOn_inv_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S)
    (hu : ∀ s ∈ S, IsUnit (M s).det) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => (M s)⁻¹ i j) S := by
  have hdet : DifferentiableOn ℂ (fun s => (M s).det) S := differentiableOn_det_of_entries h
  have hadj : DifferentiableOn ℂ (fun s => (M s).adjugate i j) S := by
    have hupd : ∀ k l, DifferentiableOn ℂ (fun s => ((M s).updateRow j (Pi.single i 1)) k l) S := by
      intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne hk]
        exact h k l
    have := differentiableOn_det_of_entries hupd
    simpa only [Matrix.adjugate_apply] using this
  have hinv : DifferentiableOn ℂ (fun s => ((M s).det)⁻¹) S :=
    hdet.fun_inv fun s hs => (hu s hs).ne_zero
  have heq : (fun s => (M s)⁻¹ i j) = fun s => ((M s).det)⁻¹ * (M s).adjugate i j := by
    funext s
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact hinv.fun_mul hadj

theorem differentiableOn_combMat_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g r : ℕ}
    {l : E → Fin r → Fin g → ℂ} {S : Set E} (ε : Matrix (Fin g) (Fin r) ℚ)
    (h : ∀ m k, DifferentiableOn ℂ (fun s => l s m k) S) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => combMat (l s) ε i j) S := by
  simp only [combMat, Matrix.of_apply]
  apply DifferentiableOn.fun_sum
  intro m _
  exact (h m i).const_mul _

theorem differentiableOn_combMat_perTau : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  intro n a g r₀ r ζ lam α φ D hζ hlam hunit
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζ.differentiableOn
  have hζe : ∀ m k, DifferentiableOn ℂ (fun z => ζ z m k) (Metric.ball 0 1) := by
    intro m k
    have h1 := differentiableOn_pi.1 hζd m
    exact differentiableOn_pi.1 h1 k
  have hA : ∀ i j, DifferentiableOn ℂ (fun z => combMat (ζ z) α i j) (Metric.ball 0 1) :=
    fun i j => differentiableOn_combMat_of_entries α hζe i j
  refine ⟨hA, ?_⟩
  intro i j
  set T : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} with hT
  have hexp : Differentiable ℂ (fun s : Fin n → ℂ => logExp a s) := by
    refine differentiable_pi.2 fun k => ?_
    simp only [logExp]
    split_ifs
    · exact (differentiable_apply k).cexp
    · exact differentiable_apply k
  have hAT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (ζ (logExp a s)) α i j) T := by
    intro i j
    exact (hA i j).comp hexp.differentiableOn (fun s hs => hs.2)
  have hinvT : ∀ i j, DifferentiableOn ℂ (fun s => (combMat (ζ (logExp a s)) α)⁻¹ i j) T :=
    differentiableOn_inv_of_entries hAT (fun s hs => hunit s hs.1)
  have hBT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (lam s) φ i j) T := by
    intro i j
    exact (differentiableOn_combMat_of_entries φ hlam i j).mono (fun s hs => hs.1)
  simp only [perTau, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.fun_sum
  intro k _
  exact (hinvT i k).fun_mul (hBT k j)

end GlobalTheory.PeriodFrame
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_rationalFrame_periodMatrix_logCover : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  atlas_forward_decl GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

theorem combMat_mul_left {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (b * ε) = combMat l ε * bᵀ.map (Rat.cast : ℚ → ℂ) := by
  have h := combMat_add_mul l ε 0 bᵀ
  have h0 : combMat l (0 : Matrix (Fin g) (Fin r) ℚ) = 0 := by
    ext k j; simp [combMat]
  rwa [h0, zero_add, zero_add, Matrix.transpose_transpose] at h

theorem combMat_add {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) :
    combMat l (ε + φ) = combMat l ε + combMat l φ := by
  ext k j
  simp [combMat, add_mul, Finset.sum_add_distrib]

theorem isUnit_det_combMat_on_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  intro n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ B hD hζ hstd hlam hc hdl hP hτ hB hper z hz
  choose I hI using hstd
  let sel : Matrix (Fin g) (Fin r₀) ℚ := Matrix.of fun j i => if i = I j then 1 else 0
  let Dl : Matrix (Fin g) (Fin g) ℂ := (sel * dl)ᵀ.map (Rat.cast : ℚ → ℂ)
  let G : Matrix (Fin g) (Fin g) ℂ := (sel * gm)ᵀ.map (Rat.cast : ℚ → ℂ)
  have hsel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, combMat (ζ z) sel = 1 := by
    intro z hz
    ext k j
    have h1 : combMat (ζ z) sel k j = ζ z (I j) k := by
      simp only [combMat, sel, Matrix.of_apply]
      rw [Finset.sum_eq_single (I j)]
      · simp
      · intro i _ hi; simp [hi]
      · simp
    rw [h1, hI j z hz, Matrix.one_apply, Pi.single_apply]
  have hBD : ∀ k, (B k).map (Int.cast : ℤ → ℂ) * Dl = 0 := by
    intro k
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, Dl, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < rk
    · simp [hdl _ l hl]
    · simp [hB k i l (Or.inr (not_lt.mp hl))]
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPc : ContinuousOn (fun z => combMat (ζ z) α) (Metric.ball (0 : Fin n → ℂ) 1) := by
    refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => ?_
    simp only [combMat, Matrix.of_apply]
    refine continuousOn_finset_sum _ fun m _ => continuousOn_const.mul ?_
    exact continuousOn_pi.1 (continuousOn_pi.1 hζ.continuousOn m) k
  have hτc : ContinuousOn τ₀ (Metric.ball (0 : Fin n → ℂ) 1) :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => (hτ k i).continuousOn
  have hQ : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
      p.1 * (G + (D : ℂ)⁻¹ • (p.2 * Dl))) := by fun_prop
  have hQc : ContinuousOn (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl)))
      (Metric.ball (0 : Fin n → ℂ) 1) := by
    have h := hQ.comp_continuousOn (hPc.prodMk hτc)
    simpa only [Function.comp_def] using h
  have key := GlobalTheory.eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix (Fin g) (Fin g) ℂ)
    (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl))) (fun _ => 1) le_rfl
    hQc continuousOn_const (by
      intro s hs hb
      have h1 := hsel _ hb
      rw [combMat_comb _ _ c sel (hlam s hs), hc, Matrix.mul_add, ← Matrix.mul_assoc sel gm, ← Matrix.mul_assoc sel dl,
        combMat_add, combMat_mul_left, combMat_mul_left, ← combMat_comb _ _ c α (hlam s hs)] at h1
      have h2 := congrArg (fun T => T * Dl) (hper s hs hb)
      simp only [perTau, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, hBD, smul_zero, Finset.sum_const_zero,
        add_zero] at h2
      rw [← h2, smul_smul, inv_mul_cancel₀ hDc, one_smul, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hP s hs), Matrix.one_mul]
      exact h1) z hz
  exact Matrix.isUnit_det_of_right_inverse key

end GlobalTheory.PeriodFrame
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_rational_combination_frame_closed_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  atlas_forward_decl GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posDef_im_on_ball_of_logExp : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  intro n a J _ _ Δ hΔ hpos z hz
  set U := Metric.ball (0 : Fin n → ℂ) 1 with hU
  have hcont : ∀ i j, ContinuousOn (fun w => Δ w i j) U := fun i j => (hΔ i j).continuousOn
  have hM : ContinuousOn (fun w => (Δ w).map Complex.im) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont i j)
  have hMT : ContinuousOn (fun w => ((Δ w).map Complex.im)ᵀ) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont j i)
  have hsymm : ((Δ z).map Complex.im)ᵀ = (Δ z).map Complex.im := by
    refine eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix J J ℝ)
      (fun w => ((Δ w).map Complex.im)ᵀ) (fun w => (Δ w).map Complex.im) le_rfl hMT hM ?_ z hz
    intro s hs _
    have h1 := (hpos s hs).1
    unfold Matrix.IsHermitian at h1
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  intro x hx
  set q : (Fin n → ℂ) → ℂ := fun w => ∑ i, ∑ j, (x i : ℂ) * Δ w i j * (x j : ℂ) with hq
  have hqim : ∀ w, (q w).im = star x ⬝ᵥ ((Δ w).map Complex.im *ᵥ x) := by
    intro w
    simp [q, dotProduct, mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum, mul_comm,
      mul_left_comm, mul_assoc]
  have hqd : DifferentiableOn ℂ q U := by
    rw [hq]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.fun_sum
    intro j _
    exact ((hΔ i j).const_mul (x i : ℂ)).mul_const (x j : ℂ)
  have hqpos : ∀ s ∈ logDom n a, 0 < (q (logExp a s)).im := by
    intro s hs
    rw [hqim]
    exact (hpos s hs).dotProduct_mulVec_pos hx
  have hqc : ContinuousOn (fun w => (q w).im) U :=
    Complex.continuous_im.comp_continuousOn hqd.continuousOn
  have hnn : ∀ w ∈ U, 0 ≤ (q w).im := by
    intro w hw
    have := eq_on_ball_of_eq_on_logExp_image n a 1 ℝ (fun w => min (q w).im 0) (fun _ => 0)
      le_rfl ((continuous_id.min continuous_const).comp_continuousOn hqc) continuousOn_const
      (fun s hs _ => min_eq_right (hqpos s hs).le) w hw
    exact (min_eq_right_iff.1 this)
  rw [← hqim]
  rcases (hnn z hz).lt_or_eq with h | h0
  · exact h
  exfalso
  set F : (Fin n → ℂ) → ℂ := fun w => Complex.exp (Complex.I * q w) with hF
  have hFn : ∀ w, ‖F w‖ = Real.exp (-(q w).im) := by
    intro w
    simp [F, Complex.norm_exp, Complex.I_mul_re]
  have hFd : DifferentiableOn ℂ F U := (hqd.const_mul Complex.I).cexp
  have hmax : IsMaxOn (norm ∘ F) U z := by
    intro w hw
    simp only [Set.mem_setOf_eq, Function.comp, hFn, ← h0, neg_zero]
    exact Real.exp_le_exp.2 (by linarith [hnn w hw])
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : Fin n → ℂ) 1).isPreconnected
    Metric.isOpen_ball hFd hz hmax
  obtain ⟨s, hs⟩ := (GlobalTheory.ShFam.Hor.Mark.nonempty_logDom : (logDom n a).Nonempty)
  have hmem : logExp a s ∈ U := GlobalTheory.ShFam.Hor.Mark.logExp_mem hs
  have h2 := congrArg norm (heq hmem)
  simp only [Function.const_apply, hFn, ← h0, neg_zero] at h2
  have h3 : (q (logExp a s)).im = 0 := by
    have := Real.exp_injective h2
    linarith
  exact (hqpos s hs).ne' h3

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_imPart_on_polydisc_of_punctured_cover : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  atlas_forward_decl GlobalTheory.posDef_im_on_ball_of_logExp
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PeriodFrame

theorem combMat_mulVec_eq_sum {g r : ℕ} (l : Fin r → Fin g → ℂ) (φ : Matrix (Fin g) (Fin r) ℚ) (v : Fin g → ℂ) :
    combMat l φ *ᵥ v = ∑ m, (∑ i, (φ i m : ℂ) * v i) • l m := by
  ext k
  simp only [combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem exists_nat_mul_int {r : ℕ} (u : Fin r → ℚ) : ∃ N : ℕ, 0 < N ∧ ∀ m, ∃ k : ℤ, (N : ℚ) * u m = k := by
  refine ⟨∏ m, (u m).den, Finset.prod_pos fun m _ => (u m).den_pos, fun m => ?_⟩
  refine ⟨(∏ j ∈ Finset.univ.erase m, (u j).den : ℕ) * (u m).num, ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ m)]
  push_cast
  rw [_root_.mul_assoc, _root_.mul_comm ((u m).den : ℚ), Rat.mul_den_eq_num]

end GlobalTheory.PeriodFrame

theorem GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous : ∀ (n a g r₀ r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (rk D : ℕ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → Mᵀ = -M → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) → 0 < D → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → ∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 1) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).mulVec (fun j => (v j : ℂ)) = F (logExp a s) := by
  intro n a g r₀ r K ζ lam M c α φ rk D hK hζa hζK hζ0 hlam hζc hM hφ hrk hD hdet v hv hsupp F hF heq
  set u : Fin r → ℚ := fun m => ∑ i, φ i m * (v i : ℚ) with hu
  obtain ⟨N, hN0, hNint⟩ := GlobalTheory.PeriodFrame.exists_nat_mul_int u
  choose kk hkk using hNint
  set W : (Fin n → ℂ) → Fin g → ℂ := fun z => ((N : ℂ) / D) • (GlobalTheory.PeriodFrame.combMat (ζ z) α *ᵥ F z) with hW
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hζc0 : ContinuousAt ζ 0 := (hζa 0 h0).continuousAt
  have hFc0 : ContinuousAt F 0 := hF.continuousAt (Metric.isOpen_ball.mem_nhds h0)
  have hWc : ContinuousAt W 0 := by
    have h1 : ∀ m k, ContinuousAt (fun z => ζ z m k) 0 := fun m k =>
      (continuous_apply k).continuousAt.comp ((continuous_apply m).continuousAt.comp hζc0)
    have h2 : ∀ i, ContinuousAt (fun z => F z i) 0 := fun i => (continuous_apply i).continuousAt.comp hFc0
    refine continuousAt_pi.2 fun k => ?_
    simp only [hW, GlobalTheory.PeriodFrame.combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hlK : ∀ᶠ b in 𝓝 (0 : Fin n → ℂ), ∀ j, ζ b j ∈ K b := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with b hb using hζK b hb
  have hev := IsLatFam.eventually_intComb hK h0 hζc0 hlK hζ0 (W 0)
  have ht : Filter.Tendsto (fun z => (z, W z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 ((0 : Fin n → ℂ), W 0)) :=
    (continuousAt_id.prodMk hWc).tendsto
  have hev2 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
      (W z ∈ K z → ∃ m : Fin r₀ → ℤ, W z = ∑ j, m j • ζ z j) :=
    Filter.Eventually.and (Metric.isOpen_ball.mem_nhds h0 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1)
      (ht.eventually hev)
  set s : ℝ → Fin n → ℂ := fun R k => if (k : ℕ) < a then -(R : ℂ) else 0 with hs
  have hsdom : ∀ R : ℝ, 0 < R → s R ∈ logDom n a := by
    intro R hR k
    by_cases hk : (k : ℕ) < a
    · simp [hs, hk, hR]
    · simp [hs, hk]
  have hslim : Filter.Tendsto (fun R => logExp a (s R)) Filter.atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hs, hk, if_true, Pi.zero_apply]
      have h3 : Filter.Tendsto (fun R : ℝ => ((Real.exp (-R) : ℝ) : ℂ)) Filter.atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      simpa [Complex.ofReal_exp] using h3
    · simp [logExp, hs, hk]
  obtain ⟨R, ⟨hzb, hzK⟩, hR0⟩ := ((hslim.eventually hev2).and (Filter.eventually_gt_atTop 0)).exists
  have hs0 := hsdom R hR0
  have he := heq (s R) hs0 hzb
  have hWz : W (logExp a (s R)) = ∑ m, ((kk m : ℤ) : ℂ) • lam (s R) m := by
    have hP := hdet (s R) hs0
    have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hsm : ∀ (c : ℂ) (A : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ), (c • A) *ᵥ x = c • (A *ᵥ x) := by
      intro c A x; ext p; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]
    simp only [hW]
    rw [← he, GlobalTheory.PeriodFrame.perTau, Matrix.mulVec_mulVec, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, hsm, smul_smul,
      GlobalTheory.PeriodFrame.combMat_mulVec_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    have h4 := congrArg (Rat.cast : ℚ → ℂ) (hkk m)
    push_cast [hu] at h4
    rw [← h4]
    field_simp

  have hWK : W (logExp a (s R)) ∈ K (logExp a (s R)) :=
    ((hlam (s R) hs0).2 _).2 ⟨kk, by rw [hWz]; exact Finset.sum_congr rfl fun m _ => Int.cast_smul_eq_zsmul ℂ _ _⟩
  obtain ⟨mm, hmm⟩ := hzK hWK
  have hcomb : ∑ j, kk j • lam (s R) j = ∑ j, (∑ i, mm i * c i j) • lam (s R) j := by
    have e1 : ∑ j, kk j • lam (s R) j = W (logExp a (s R)) := by
      rw [hWz]; exact Finset.sum_congr rfl fun m _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
    rw [e1, hmm]
    simp only [hζc (s R) hs0, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hkc : ∀ j, kk j = ∑ i, mm i * c i j := by
    have hli := (hlam (s R) hs0).1
    have h5 := Fintype.linearIndependent_iff.1 hli (fun j => ((kk j - ∑ i, mm i * c i j : ℤ) : ℝ)) (by
      simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, hcomb, sub_self])
    intro j
    have h6 := h5 j
    have h7 : kk j - ∑ i, mm i * c i j = 0 := by exact_mod_cast h6
    exact sub_eq_zero.1 h7
  set cq := c.map (Int.cast : ℤ → ℚ) with hcq
  set Mq := M.map (Int.cast : ℤ → ℚ) with hMq
  set vq : Fin g → ℚ := fun i => (v i : ℚ) with hvq
  set mq : Fin r₀ → ℚ := fun i => (mm i : ℚ) with hmq
  have hvec : Matrix.vecMul ((N : ℚ) • vq) φ = Matrix.vecMul mq cq := by
    ext j
    have h6 := hkk j
    rw [hkc j] at h6
    push_cast at h6
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, hcq, hvq, hmq, Matrix.map_apply]
    rw [← h6, hu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hskew : cq * (Mq * (α * cq)ᵀ) = -((α * cq) * Mq * cqᵀ)ᵀ := by
    have hMt : Mqᵀ = -Mq := by
      ext i j
      have h := congrFun (congrFun hM i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
      simp [hMq, Matrix.transpose_apply, h]
    rw [Matrix.transpose_mul (α * cq * Mq), Matrix.transpose_transpose, Matrix.transpose_mul (α * cq) Mq, hMt]
    simp [Matrix.neg_mul, Matrix.mul_neg]
  have hfin := congrArg (fun x => Matrix.vecMul x (Mq * (α * cq)ᵀ)) hvec
  simp only [Matrix.vecMul_vecMul] at hfin
  rw [show φ * (Mq * (α * cq)ᵀ) = 1 by rw [← Matrix.mul_assoc, hφ], Matrix.vecMul_one, hskew] at hfin
  apply hv
  funext i
  by_cases hi : i.val < rk
  · have h7 := congrFun hfin i
    have h8 : Matrix.vecMul mq (-((α * cq) * Mq * cqᵀ)ᵀ) i = 0 := by
      simp only [Matrix.vecMul, dotProduct, Matrix.neg_apply, Matrix.transpose_apply, hrk i hi, neg_zero, mul_zero,
        Finset.sum_const_zero]
    rw [h8] at h7
    simp only [Pi.smul_apply, smul_eq_mul, hvq] at h7
    have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
    have h9 := (mul_eq_zero.1 h7).resolve_left hN
    simpa using h9
  · exact hsupp i (not_lt.1 hi)
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_periodMatrix_intVec_continuous_boundary : ∀ (n a g r₀ r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (rk D : ℕ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → Mᵀ = -M → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) → 0 < D → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → ∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 1) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).mulVec (fun j => (v j : ℂ)) = F (logExp a s) := by
  atlas_forward_decl GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PeriodFrame.exists_frame_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (d ρ₁ : ℝ) (P τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (Δ : (Fin n → ℂ) → Matrix {j : Fin g // rk ≤ j.val} {j : Fin g // rk ≤ j.val} ℂ), 0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < d ∧ rk ≤ g ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, IsUnit (P z).det) ∧ (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) ∧ (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (((τ s).map Complex.im).map Complex.ofReal)⁻¹) ∧ ContinuousOn Δ (Metric.ball 0 ρ₁) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, ((Δ z).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).submatrix Subtype.val Subtype.val = Δ (logExp a s)) ∧ (∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 ρ₁) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).mulVec (fun j => (v j : ℂ)) = F (logExp a s)) := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlamc hlam hH htor
  obtain ⟨hDo, hDc, hDan, hDmaps⟩ := GlobalTheory.logDom_chart_props n a
  have hlogc : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) :=
    continuous_iff_continuousAt.2 fun s => (hDan s).continuousAt
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    by_cases h : (k : ℕ) < a <;> simp [s₀, h]
  obtain ⟨hr, hlamR, hlamD⟩ := GlobalTheory.T.punctPolydiscCover_latticeBasis_real_holomorphic n a g r K lam hK hlamc hlam
  have hlB : ∀ b ∈ logDom n a, IsLatBasis (K (logExp a b)) (lam b) := fun b hb => ⟨hlamR b hb, (hlam b hb).2.2⟩
  have hmemL : ∀ b ∈ logDom n a, ∀ i, lam b i ∈ K (logExp a b) := fun b hb i =>
    ((hlam b hb).2.2 _).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hpre : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hζc : ContinuousOn (fun s => ζ (logExp a s)) (logDom n a) := hζ.continuousOn.comp hlogc.continuousOn hDmaps
  have hcex' : ∀ i : Fin r₀, ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, m j • lam b j := fun i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => ζ (logExp a b) i) s₀ hpre hlamc ((continuous_apply i).comp_continuousOn hζc) hlB
      (fun b hb => hζK _ (hDmaps hb) i) hs₀
  have hcex : ∃ c : Matrix (Fin r₀) (Fin r) ℤ, ∀ i, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, c i j • lam b j := by
    choose c hc using hcex'
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcex
  have hsh := fun (k : Fin a) (s : Fin n → ℂ) (hs : s ∈ logDom n a) => GlobalTheory.PeriodFrame.shift_mem ha k hs
  have hTex' : ∀ (k : Fin a) (i : Fin r), ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, m j • lam b j := fun k i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i) s₀ hpre hlamc
      ((continuous_apply i).comp_continuousOn
        (hlamc.comp (continuous_add_right _).continuousOn fun b hb => (hsh k b hb).1))
      hlB (fun b hb => by rw [← (hsh k b hb).2]; exact hmemL _ (hsh k b hb).1 i) hs₀
  have hTex : ∃ T : Fin a → Matrix (Fin r) (Fin r) ℤ, ∀ k i, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, T k i j • lam b j := by
    choose T hT using hTex'
    exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := hTex
  obtain ⟨Hm₀, hH₀h, hH₀p, hH₀l⟩ := hH s₀ hs₀
  have hM₀ := hH₀l s₀ hs₀ rfl
  have hMa : Mᵀ = -M := GlobalTheory.T.hermForm_im_intMatrix_transpose_neg g r Hm₀ (lam s₀) M hH₀h hM₀
  have hMd : M.det ≠ 0 :=
    GlobalTheory.det_ne_zero_of_im_hermForm_eq_int g r Hm₀ (lam s₀) M hH₀p (hlamR s₀ hs₀) (hlam s₀ hs₀).2.1 hM₀
  have hTM : ∀ k, T k * M * (T k)ᵀ = M := by
    intro k
    have h1 := GlobalTheory.T.hermForm_im_intCombination_eq_conj_mul g r r Hm₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (T k) M (fun i => hT k i s₀ hs₀) hM₀
    have h2 := hH₀l _ (hsh k s₀ hs₀).1 (hsh k s₀ hs₀).2
    ext i j
    have h3 := (h1 i j).symm.trans (h2 i j)
    exact_mod_cast h3
  have hcT : ∀ k, c * T k = c := fun k =>
    GlobalTheory.T.coeffMatrix_mul_eq_of_same_intCombinations g r r₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (ζ (logExp a s₀)) c (T k) (hlam s₀ hs₀).1 (fun i => hT k i s₀ hs₀) (fun i => hc i s₀ hs₀)
      (fun i => by rw [← (hsh k s₀ hs₀).2]; exact hc i _ (hsh k s₀ hs₀).1)
  have hcLI : LinearIndependent ℚ (fun i j => (c i j : ℚ)) :=
    GlobalTheory.rowsInd_rat_of_real g r r₀ (lam s₀) (ζ (logExp a s₀)) c (hζi _ (hDmaps hs₀)) (fun i => hc i s₀ hs₀)
  have hco := GlobalTheory.CoisoCount.coisotropic_of_torsion_count r r₀ M c hMd hcLI (by
    intro N hN
    obtain ⟨S, hcard, hS⟩ := htor N hN
    refine ⟨S, by rw [hr]; exact hcard, fun u u' hu => ?_⟩
    obtain ⟨m, hm⟩ := hS u u' hu s₀ hs₀ Hm₀ hM₀
    rw [GlobalTheory.T.hermForm_im_intCombination_dotProduct g r r₀ Hm₀ (lam s₀) (ζ (logExp a s₀)) c M (fun i => hc i s₀ hs₀) hM₀ u u'] at hm
    exact ⟨m, by exact_mod_cast hm⟩)
  obtain ⟨rk, α, φ, β, gm, dl, hrk, hN1, hN2, hN3, hN4, hN5, hN6, hN7⟩ := GlobalTheory.T.exists_rational_symplecticBasis_adapted_coisotropic g r r₀ M c hr hMa hMd hcLI hco
  choose b hb using fun k => GlobalTheory.T.intIsometry_fixing_rowSpace_symplectic_shift g r r₀ rk M (T k) c α φ β hr hMa (hTM k) (hcT k) hN1 hN2 hN3 hN5
  obtain ⟨D, Bz, hD, hBz⟩ := GlobalTheory.T.exists_common_denominator_rat_matrices a g b
  have hBzs : ∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → Bz k j l = 0 := by
    intro k j l h
    have h1 := hBz k j l
    rw [(hb k).1 j l h, mul_zero] at h1
    exact_mod_cast h1
  have hPeq : ∀ s ∈ logDom n a, GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α =
      GlobalTheory.PeriodFrame.combMat (lam s) (α * c.map (Int.cast : ℤ → ℚ)) :=
    fun s hs => GlobalTheory.PeriodFrame.combMat_comb _ _ c α (fun i => hc i s hs)
  have hRie : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧
      IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det ∧ (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef ∧
      (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀᴴ =
        ((D : ℝ) : ℂ) • (((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).map Complex.ofReal)⁻¹ := by
    intro s hs
    obtain ⟨Hm, h1, h2, h3⟩ := hH s hs
    refine ⟨Hm, h3 s hs rfl, ?_⟩
    unfold GlobalTheory.PeriodFrame.perTau
    rw [hPeq s hs]
    exact GlobalTheory.T.riemannRelations_rationalCombinationFrame g r Hm M (lam s) _ φ D hD h1 h2 (hlamR s hs) (h3 s hs rfl) hN1 hN2 hN3
  have hdet : ∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det := fun s hs => by
    obtain ⟨_, _, h, _⟩ := hRie s hs
    exact h
  obtain ⟨hPd, hτd⟩ := GlobalTheory.T.differentiableOn_rationalFrame_periodMatrix_logCover n a g r₀ r ζ lam α φ D hζ hlamD hdet
  have hτsm : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef := fun s hs _ => by
    obtain ⟨_, _, _, h1, h2, _⟩ := hRie s hs
    exact ⟨h1, h2⟩
  have hmono : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∀ k : Fin a,
      GlobalTheory.PeriodFrame.perTau a ζ lam α φ D (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) =
        GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s + (Bz k).map (Int.cast : ℤ → ℂ) := by
    intro s hs _ k
    unfold GlobalTheory.PeriodFrame.perTau
    rw [(hsh k s hs).2, hPeq s hs,
      GlobalTheory.PeriodFrame.combMat_comb (lam (s + _)) (lam s) (T k) φ (fun i => hT k i s hs), (hb k).2]
    exact GlobalTheory.PeriodFrame.combMat_shift (lam s) _ φ (b k) D (Bz k) (hPeq s hs ▸ hdet s hs) (hBz k)
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ :=
    GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha 1 (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D) Bz one_pos le_rfl hτd hτsm hmono
  have hPu : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det :=
    GlobalTheory.T.isUnit_det_rational_combination_frame_closed_ball n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ Bz hD hζ hstd (fun s hs i => hc i s hs) hN7 hN6 hdet hτ₀d
      hBzs hτ₀e
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 1) := fun j l => (hτ₀d j l).continuousOn
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
        (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) =
        (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
          (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) := by
    intro s hs hz
    rw [hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hBzs _ j l (Or.inl hj)]
  refine ⟨rk, (D : ℝ), 1, fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α, GlobalTheory.PeriodFrame.perTau a ζ lam α φ D, Bz,
    fun z => (τ₀ z).submatrix Subtype.val Subtype.val, one_pos, le_rfl, by exact_mod_cast hD, hrk, hPd, hPu, hτd,
    hτsm, hmono, hBzs, ?_, ?_, ?_, hagree, ?_⟩
  · intro s hs hz Hm hHm
    obtain ⟨Hm', h1, _, _, _, h5⟩ := hRie s hs
    have hHH : Hm = Hm' :=
      GlobalTheory.T.complexMatrix_eq_of_hermForm_im_eq_real_span g r Hm Hm' (lam s) (hlam s hs).2.1 (fun i j => (hHm i j).trans (h1 i j).symm)
    subst hHH
    exact h5
  · exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1
  · refine GlobalTheory.T.posDef_imPart_on_polydisc_of_punctured_cover n a {j : Fin g // rk ≤ j.val} (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g))
      (fun j l => hτ₀d j.1 l.1) ?_
    intro s hs
    rw [← hagree s hs (hDmaps hs)]
    exact (hτsm s hs (hDmaps hs)).2.submatrix Subtype.val_injective
  · exact GlobalTheory.T.not_periodMatrix_intVec_continuous_boundary n a g r₀ r K ζ lam M c α φ rk D hK hζ hζK hζ0 (fun s hs => ⟨hlamR s hs, (hlam s hs).2.2⟩)
      (fun s hs i => hc i s hs) hMa hN3 hN4 hD hdet
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodFrame_of_holomorphicLatticeFamily : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (d ρ₁ : ℝ) (P τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (Δ : (Fin n → ℂ) → Matrix {j : Fin g // rk ≤ j.val} {j : Fin g // rk ≤ j.val} ℂ), 0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < d ∧ rk ≤ g ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, IsUnit (P z).det) ∧ (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) ∧ (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (((τ s).map Complex.im).map Complex.ofReal)⁻¹) ∧ ContinuousOn Δ (Metric.ball 0 ρ₁) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, ((Δ z).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).submatrix Subtype.val Subtype.val = Δ (logExp a s)) ∧ (∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 ρ₁) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).mulVec (fun j => (v j : ℂ)) = F (logExp a s)) := by
  atlas_forward_decl GlobalTheory.PeriodFrame.exists_frame_of_latFam
end
