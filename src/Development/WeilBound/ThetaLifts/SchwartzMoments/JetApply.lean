module

import Development.WeilBound.ThetaLifts.SmallCones.SchInt
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKOwn

open MeasureTheory

namespace SchI

open scoped ContDiff NNReal BoundedContinuousFunction
open Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cd (f : SchwartzMap V ℂ) (j : ℕ) : ContDiff ℝ j f := by
  exact f.smooth j

def jet (k j : ℕ) (f : SchwartzMap V ℂ) : V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖x‖ ^ k • iteratedFDeriv ℝ j f x)
    ((continuous_norm.pow k).smul ((cd f j).continuous_iteratedFDeriv le_rfl)) (SchwartzMap.seminorm ℂ k j f) fun x => by
      rw [norm_smul, norm_pow, norm_norm]
      exact SchwartzMap.le_seminorm ℂ k j f x

theorem jet_apply (k j : ℕ) (f : SchwartzMap V ℂ) (x : V) : jet k j f x = ‖x‖ ^ k • iteratedFDeriv ℝ j f x := rfl

theorem norm_jet (k j : ℕ) (f : SchwartzMap V ℂ) : ‖jet k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  refine le_antisymm ?_ ?_
  · exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _
  · refine SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _) fun x => ?_
    have h := (jet k j f).norm_coe_le_norm x
    rw [jet_apply, norm_smul, norm_pow, norm_norm] at h
    exact h

def J (k j : ℕ) : SchwartzMap V ℂ →L[ℂ] V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (jet k j)
    (fun f g => by
      ext1 x
      rw [BoundedContinuousFunction.add_apply, jet_apply, jet_apply, jet_apply, ← smul_add]
      exact congrArg _ (iteratedFDeriv_add_apply (cd f j).contDiffAt (cd g j).contDiffAt))
    (fun a f => by
      ext1 x
      rw [BoundedContinuousFunction.smul_apply, jet_apply, jet_apply, RingHom.id_apply, smul_comm a]
      exact congrArg _ (iteratedFDeriv_const_smul_apply (cd f j).contDiffAt))
    ⟨{(k, j)}, 1, zero_le_one, fun f => by rw [norm_jet, Finset.sup_singleton, one_mul]; rfl⟩

theorem J_apply (k j : ℕ) (f : SchwartzMap V ℂ) : J k j f = jet k j f := rfl

variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)

include hG hI

theorem int_J (k j : ℕ) : Integrable (fun a => J k j (G a)) μ := by
  refine Integrable.mono' (hI k j) ((J k j).continuous.comp hG).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => le_of_eq ?_)
  rw [J_apply, norm_jet]

omit hI in
theorem cont_D (j : ℕ) (x : V) : Continuous fun a => iteratedFDeriv ℝ j (G a) x := by
  have h : (fun a => iteratedFDeriv ℝ j (G a) x) = fun a => J 0 j (G a) x := by
    funext a
    rw [J_apply, jet_apply, pow_zero, one_smul]
  rw [h]
  exact (continuous_eval_const x).comp ((J 0 j).continuous.comp hG)

omit hG hI in
theorem bd_D (f : SchwartzMap V ℂ) (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
  have h := SchwartzMap.le_seminorm ℂ 0 j f x
  rwa [pow_zero, one_mul] at h

theorem int_D (j : ℕ) (x : V) : Integrable (fun a => iteratedFDeriv ℝ j (G a) x) μ := by
  exact Integrable.mono' (hI 0 j) (cont_D hG j x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => bd_D (G a) j x)

theorem deriv_D (j : ℕ) (x : V) : HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ j (G a) y ∂μ)
    (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft x := by
  apply PositivityTheory.ThKCT.SchI.deriv_D <;> assumption

theorem taylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ := by
  refine ⟨?_, fun m _ x => deriv_D hG hI m x, fun m _ => ?_⟩
  · intro x
    show (∫ a, iteratedFDeriv ℝ 0 (G a) x ∂μ) 0 = ∫ a, G a x ∂μ
    rw [ContinuousMultilinearMap.integral_apply (int_D hG hI 0 x)]
    simp only [iteratedFDeriv_zero_apply]
  · exact continuous_iff_continuousAt.2 fun x => (deriv_D hG hI m x).continuousAt

theorem eval_int (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by
  have h1 : (∫ a, J k j (G a) ∂μ) x = ∫ a, J k j (G a) x ∂μ :=
    ((BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm (int_J hG hI k j)).symm
  rw [h1, ← (taylor hG hI).eq_iteratedFDeriv (m := j) (by exact_mod_cast le_top) x]
  simp only [J_apply, jet_apply]
  exact integral_smul _ _

theorem exists_int : ∃ f : SchwartzMap V ℂ, ∀ k j, J k j f = ∫ a, J k j (G a) ∂μ := by
  refine ⟨⟨fun x => ∫ a, G a x ∂μ, (taylor hG hI).contDiff, fun k n => ⟨‖∫ a, J k n (G a) ∂μ‖, fun x => ?_⟩⟩,
    fun k j => ?_⟩
  · have h := (∫ a, J k n (G a) ∂μ).norm_coe_le_norm x
    rw [eval_int hG hI, norm_smul, norm_pow, norm_norm] at h
    exact h
  · ext1 x
    rw [J_apply, jet_apply, eval_int hG hI]
    rfl

omit hG hI in
theorem factor (T : SchwartzMap V ℂ →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (T' : (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, T f = T' fun i => J i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  let Φ : SchwartzMap V ℂ →ₗ[ℂ] (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) :=
    LinearMap.pi fun i => (J i.1.1 i.1.2 : SchwartzMap V ℂ →L[ℂ] _).toLinearMap
  have hbound : ∀ f, ‖T f‖ ≤ C * ‖Φ f‖ := by
    intro f
    have h1 : ‖T f‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) f := hC f
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    have h2 : ‖J i.1 i.2 f‖ ≤ ‖Φ f‖ := norm_le_pi_norm (Φ f) ⟨i, hi⟩
    rw [J_apply, norm_jet] at h2
    exact h2
  have hker : LinearMap.ker Φ ≤ LinearMap.ker T.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have h := hbound f
    rw [hf, norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  let g₀ : LinearMap.range Φ →ₗ[ℂ] ℂ :=
    (LinearMap.ker Φ).liftQ T.toLinearMap hker ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hg₀ : ∀ f, g₀ ⟨Φ f, LinearMap.mem_range_self Φ f⟩ = T f := by
    intro f
    simp only [g₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hg₀b : ∀ v, ‖g₀ v‖ ≤ C * ‖v‖ := by
    rintro ⟨_, f, rfl⟩
    show ‖g₀ ⟨Φ f, LinearMap.mem_range_self Φ f⟩‖ ≤ C * ‖Φ f‖
    rw [hg₀]
    exact hbound f
  obtain ⟨T', hT', -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (g₀.mkContinuous C hg₀b)
  refine ⟨s, T', fun f => ?_⟩
  have h := hT' ⟨Φ f, LinearMap.mem_range_self Φ f⟩
  rw [LinearMap.mkContinuous_apply, hg₀] at h
  exact h.symm

end SchI


open MeasureTheory in
theorem weakInt :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (α : Type) [TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α) (G : α → SchwartzMap V ℂ), Continuous G →
    (∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ) →
    ∃ f : SchwartzMap V ℂ, ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Integrable (fun a => T (G a)) μ ∧ T f = ∫ a, T (G a) ∂μ := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT'⟩ := SchI.factor T
  have hsplit : ∀ g : SchwartzMap V ℂ, T g = ∑ i : s, T' (Pi.single i (SchI.J i.1.1 i.1.2 g)) := by
    intro g

    rw [hT', ← map_sum, Finset.univ_sum_single]
  have hint : ∀ i : s, Integrable (fun a => T' (Pi.single i (SchI.J i.1.1 i.1.2 (G a)))) μ := fun i =>
    (T'.comp (ContinuousLinearMap.single ℂ _ i)).integrable_comp
      (SchI.int_J hG hI _ _)
  have hTG : (fun a => T (G a)) = fun a => ∑ i : s, T' (Pi.single i (SchI.J i.1.1 i.1.2 (G a))) :=
    funext fun a => hsplit (G a)
  refine ⟨by rw [hTG]; exact integrable_finsetSum _ fun i _ => hint i, ?_⟩
  rw [hTG, integral_finsetSum _ fun i _ => hint i, hsplit f]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf]
  exact ((T'.comp (ContinuousLinearMap.single ℂ _ i)).integral_comp_comm
    (SchI.int_J hG hI _ _)).symm

end PositivityTheory.ThKOwn

end
