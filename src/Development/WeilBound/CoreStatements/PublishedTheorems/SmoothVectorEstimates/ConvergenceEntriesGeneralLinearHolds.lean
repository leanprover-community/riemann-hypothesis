import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.LieAlgebraAction
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorsIntertwiner
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnitChartOperator
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FourierIntegralBound
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ConjugationOnUnits
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PositiveMatrixBlocks
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CornerBlockIndex
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.LatticeLastEntry
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CornerGLContinuity
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InverseDerivativeContinuity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalAlmostEverywhereOfBounded
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AveragingProjection
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenfunctionsClosed
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerFunctional
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RtMulApply
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CharacterNondegenerate
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnipotentCharacter
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GeneralLinearEntryConvergence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensChLift
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GoodInverseDenseRange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeetOfSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfToL2MemIrreducible
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatakeStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace HaarPairing

open scoped FourierTransform RealInnerProductSpace Real SchwartzMap

theorem inv_E {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ w, 𝐞 ⟪w, v⟫ • (∫ z, 𝐞 (-⟪z, w⟫) • g z) = g v := by
  have hI : Integrable (𝓕 g) := by
    let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := 𝓕 (hc.toSchwartzMap hg)
    have e : (𝓕 g) = ⇑G := by
      simp only [G, SchwartzMap.fourier_coe]; rfl
    rw [e]; exact G.integrable
  have h := congrFun (hg.continuous.fourierInv_fourier_eq
    (hg.continuous.integrable_of_hasCompactSupport hc) hI) v
  rw [Real.fourierInv_eq] at h
  simpa only [Real.fourier_eq] using h

theorem haar_E {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {d : ℕ}
    (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ h : EuclideanSpace ℝ (Fin d) → ℂ,
      ∫ x, h (e x) ∂μ = ((c : ℝ) : ℂ) * ∫ z, h z := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set c := Measure.addHaarScalarFactor (μ.map e) volume with hc
  have hm : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', fun h => ?_⟩
  have key : ∫ x, h (e x) ∂μ = ∫ z, h z ∂(μ.map e) :=
    (e.toHomeomorph.measurableEmbedding.integral_map h).symm
  rw [key, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem pair {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ T A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x y, β x y = 2 * π * ⟪T x, A y⟫ := by
  let T : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let φ : V → StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := fun y =>
    (2 * π)⁻¹ • (β.flip y).comp (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)
  have φadd : ∀ y y', φ (y + y') = φ y + φ y' := by
    intro y y'; simp only [φ, map_add, ContinuousLinearMap.add_comp, smul_add]
  have φsmul : ∀ (r : ℝ) y, φ (r • y) = r • φ y := by
    intro r y; simp only [φ, map_smul, ContinuousLinearMap.smul_comp, smul_comm r]
  let L : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ _).symm (φ y)
      map_add' := fun y y' => by simp only [φadd, map_add]
      map_smul' := fun r y => by
        simp only [φsmul, LinearIsometryEquiv.map_smulₛₗ, RingHom.id_apply, RCLike.conj_to_real] }
  have hL : ∀ x y, ⟪T x, L y⟫ = (2 * π)⁻¹ * β x y := by
    intro x y
    rw [real_inner_comm]
    change ⟪(InnerProductSpace.toDual ℝ _).symm (φ y), T x⟫ = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp [φ]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hβ
    intro x
    have h1 := hL x y
    rw [hy, inner_zero_right] at h1
    have hp : (2 * π)⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left hp
  let A := (L.linearEquivOfInjective hinj finrank_euclideanSpace_fin.symm).toContinuousLinearEquiv
  refine ⟨T, A, fun x y => ?_⟩
  have hA : A y = L y := rfl
  rw [hA, hL]
  field_simp

end HaarPairing

theorem haar_measure_pairing : S5 := by
  intro V _ _ _ _ _ μ _ β hβ
  obtain ⟨T, A, hTA⟩ := HaarPairing.pair β hβ
  obtain ⟨c1, hc1, h1⟩ := HaarPairing.haar_E μ T
  obtain ⟨c2, hc2, h2⟩ := HaarPairing.haar_E μ A
  refine ⟨((c1 : ℝ) : ℂ) * ((c2 : ℝ) : ℂ), mul_ne_zero (by exact_mod_cast hc1) (by exact_mod_cast hc2),
    fun f hf hc ξ => ?_⟩
  set g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ := f ∘ T.symm with hg_def
  have hgs : ContDiff ℝ ∞ g := hf.comp T.symm.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph T.symm.toHomeomorph
  have hFT : ∀ y, FT μ β f y = ((c1 : ℝ) : ℂ) *
      ∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z := by
    intro y
    rw [FT, ← h1 (fun z => Real.fourierChar (-inner ℝ z (A y)) • g z)]
    congr 1 with x
    simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def,
      Real.fourierChar_apply, smul_eq_mul, hTA]
    push_cast
    ring_nf
  have step : ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ =
      ((c1 : ℝ) : ℂ) * ∫ y, Real.fourierChar (inner ℝ (A y) (T ξ)) •
        (∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z) ∂μ := by
    rw [← integral_const_mul]
    congr 1 with y
    simp only [hFT, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hTA, real_inner_comm (A y)]
    push_cast
    ring_nf
  have h2' := h2 (fun w => Real.fourierChar (inner ℝ w (T ξ)) •
    ∫ z, Real.fourierChar (-inner ℝ z w) • g z)
  rw [step, h2', HaarPairing.inv_E g hgs hgc]
  simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  ring

end PositivityTheory.jumpWindows

end
end

section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace ExistsLogarithmLinear

theorem exists_log_lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (χ : AddChar V ℂ) (hχ : Continuous χ)
    (h0 : ∀ z, χ z ≠ 0) : ∃ L : V →L[ℝ] ℂ, ∀ z, χ z = Complex.exp (L z) := by
  let f : C(V, {z : ℂ // z ≠ 0}) := ⟨fun z => ⟨χ z, h0 z⟩, hχ.subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f]))
  have hF' : ∀ z, Complex.exp (F z) = χ z := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', AddChar.map_add_eq_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (h0 _), div_self (h0 _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

end ExistsLogarithmLinear

theorem exists_logarithm_linear : S8 := by
  intro ι _ χ hχ h1
  obtain ⟨L, hL⟩ := ExistsLogarithmLinear.exists_log_lin χ hχ (fun z h => by simpa [h] using h1 z)
  refine ⟨Complex.imCLM.comp L, fun z => ?_⟩
  have hre : (L z).re = 0 := by
    have := h1 z
    rw [hL z, Complex.norm_exp] at this
    exact Real.exp_eq_one_iff _ |>.1 this
  rw [hL z]
  congr 1
  apply Complex.ext <;> simp [hre]

end PositivityTheory.jumpWindows

end
end

section
namespace PositivityTheory.jumpWindows

theorem almost_everywhere_spherical_of_G1 : G1 → AlmostEverywhereSpherical :=
  GlobalTheory.CompanionTheory.StrongMultOne.spherical_almost_everywhere_of_bounded

end PositivityTheory.jumpWindows
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace BoundedInvariantL2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]

theorem memL2Quotient_of_bounded_left_invariant [IsFiniteMeasure (quotMeasure Γ μ)] (φ : G →ᵇ ℂ) (h : LeftInv Γ φ) : MemL2Quotient Γ μ φ := by
  refine ⟨h, MemLp.of_bound ?_ ‖φ‖ (Eventually.of_forall fun q => φ.norm_coe_le_norm q.out)⟩
  rw [aestronglyMeasurable_quotMeasure_iff_lift, h.lift_descend]
  exact φ.continuous.aestronglyMeasurable

theorem norm_toL2_sub_le_sup_norm [IsFiniteMeasure (quotMeasure Γ μ)] (φ ψ : G →ᵇ ℂ) (hφ : MemL2Quotient Γ μ φ)
    (hψ : MemL2Quotient Γ μ ψ) :
    ‖hφ.toL2 - hψ.toL2‖ ≤ (measureUnivNNReal (quotMeasure Γ μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹ * ‖φ - ψ‖ := by
  have hd : LeftInv Γ ⇑(φ - ψ) := fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g]
  have h := memL2Quotient_of_bounded_left_invariant (μ := μ) (φ - ψ) hd
  have e : hφ.toL2 - hψ.toL2 = h.toL2 := (MemLp.toLp_sub hφ.2 hψ.2).symm
  rw [e]
  exact Lp.norm_le_of_ae_bound (norm_nonneg _)
    (h.coeFn_toL2.mono fun q hq => by rw [hq]; exact (φ - ψ).norm_coe_le_norm _)

end BoundedInvariantL2

theorem bounded_invariant_functions_in_L2 : G2b := by
  intro E _ _ _ a μ _ _ H hH
  have := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  let Y : Submodule ℂ (XB E a) :=
    { carrier := {φ | ∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H}
      add_mem' := by
        rintro φ ψ ⟨h1, m1⟩ ⟨h2, m2⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(φ + ψ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g, h2.1 γ hγ g], h1.2.add h2.2⟩
        have e : h.toL2 = h1.toL2 + h2.toL2 := MemLp.toLp_add h1.2 h2.2
        exact ⟨h, e ▸ H.add_mem m1 m2⟩
      zero_mem' := by
        have h : MemL2Quotient (latticeGL E a) μ ⇑(0 : XB E a) := ⟨fun γ hγ g => rfl, MemLp.zero⟩
        have e : h.toL2 = 0 := MemLp.toLp_zero h.2
        exact ⟨h, e ▸ H.zero_mem⟩
      smul_mem' := by
        rintro c φ ⟨h1, m1⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(c • φ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g], h1.2.const_smul c⟩
        have e : h.toL2 = c • h1.toL2 := MemLp.toLp_const_smul c h1.2
        exact ⟨h, e ▸ H.smul_mem c m1⟩ }
  refine ⟨Y, ?_, ?_, fun φ => Iff.rfl⟩
  · refine IsSeqClosed.isClosed fun {x p} hx hp => ?_
    choose hxm hxH using hx
    have hpl : LeftInv (latticeGL E a) ⇑p := fun γ hγ g => by
      have t1 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p (γ * g))) :=
        ((continuous_eval_const (γ * g)).tendsto p).comp hp
      have t2 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p g)) := by
        have := ((continuous_eval_const g).tendsto p).comp hp
        refine this.congr fun n => ?_
        exact ((hxm n).1 γ hγ g).symm
      exact tendsto_nhds_unique (f := fun n => x n (γ * g)) (l := (atTop : Filter ℕ)) t1 t2
    have hp2 := BoundedInvariantL2.memL2Quotient_of_bounded_left_invariant (μ := μ) p hpl
    refine ⟨hp2, hH.1.mem_of_tendsto (f := fun n => (hxm n).toL2) (b := (atTop : Filter ℕ)) ?_
      (Eventually.of_forall hxH)⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hn : Tendsto (fun n => ‖x n - p‖) atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hp
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => BoundedInvariantL2.norm_toL2_sub_le_sup_norm (x n) p (hxm n) hp2) ?_
    simpa using hn.const_mul ((measureUnivNNReal (quotMeasure (latticeGL E a) μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹)
  · rintro g φ ⟨h, m⟩
    have m' := hH.2 g _ m
    rw [right_translate_toL2] at m'
    exact ⟨h.mul_right g, m'⟩

end PositivityTheory.jumpWindows

end
end

section
namespace PositivityTheory.jumpWindows

theorem hecke_operator_of_automorphic : G0 → G2c :=
  GlobalTheory.CompanionTheory.HeckeEigenspaces.hecke_eigenfunctions_closed

end PositivityTheory.jumpWindows
end

section
namespace PositivityTheory.jumpWindows

theorem smooth_vectors_regular_representation : S2 → G0 → G5b :=
  GlobalTheory.CompanionTheory.SmoReg.g5b

end PositivityTheory.jumpWindows
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace InfiniteFiniteFactorization

open Classical

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem stepInf (h6 : G6) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (m : Pl E → ℕ)
    (h : St ψ S Y Y' 0 m) : ∀ n, n ≤ a - 1 → St ψ S Y Y' n m := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro hn; exact h6 E a ψ hψ S Y Y' hY hY' n m (by omega) (ih (by omega))

theorem stepFin (h7 : G7) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (w : Pl E) (hw : w ∈ S)
    (n : ℕ) (m : Pl E → ℕ) (hm : m w = 0) (h : St ψ S Y Y' n m) :
    ∀ k, k ≤ a - 1 → St ψ S Y Y' n (Function.update m w k) := by
  intro k
  induction k with
  | zero => intro _; rw [Function.update_eq_self_iff.mpr hm.symm]; exact h
  | succ k ih =>
    intro hk
    have h' := h7 E a ψ hψ S Y Y' hY hY' n (Function.update m w k) w hw
      (by simp only [Function.update_self]; omega) (ih (by omega))
    simpa only [Function.update_self, Function.update_idem] using h'

end InfiniteFiniteFactorization

open InfiniteFiniteFactorization in
theorem whittaker_factorization_places : G6 → G7 → FourierInductionSteps := by
  classical
  intro h6 h7 E _ _ _ a ψ hψ S Y Y' hY hY' h0
  have h1 := stepInf h6 hψ hY hY' (fun _ => 0) h0 (a - 1) le_rfl
  have key : ∀ T : Finset (Pl E), T ⊆ S →
      St ψ S Y Y' (a - 1) (fun w => if w ∈ T then a - 1 else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      simpa using h1
    · intro x T hx ih hT
      have h := stepFin h7 hψ hY hY' x (hT (Finset.mem_insert_self x T)) (a - 1)
        (fun w => if w ∈ T then a - 1 else 0) (by simp [hx])
        (ih (subset_trans (Finset.subset_insert x T) hT)) (a - 1) le_rfl
      convert h using 1
      funext w
      by_cases hw : w = x
      · subst hw; simp
      · simp [hw]
  exact key S subset_rfl

end PositivityTheory.jumpWindows

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace SmoothVectorOrbit

theorem orb_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) :
    orb ρ (c • v) = c • orb ρ v := by
  funext M
  simp only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]
  split_ifs <;> simp

theorem smV_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) (h : SmV ρ v) : SmV ρ (c • v) := by
  unfold PositivityTheory.jumpWindows.SmV at h ⊢
  rw [PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]
  exact h.const_smul c

end SmoothVectorOrbit

theorem smooth_vector_orbit_invariance : G0 → G5 → G5b → G9 → PlacewiseToOutsideS → G8 := by
  intro hAC hSW hSP hWS hWV
  unfold PositivityTheory.jumpWindows.G8 PositivityTheory.jumpWindows.ForE
  intro E _ _ _ a ψ hψ S hS Y hY φ hφY hφ0 hφsm hφsph hφeig
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hreg, -⟩ := hAC E a
  obtain ⟨hΛ, htr, -, hW⟩ := hSW E a ψ hψ
  obtain ⟨hsmooth, hsph, hsph_smul, -, -⟩ := hSP E a S
  obtain ⟨-, hYtr, hYmir⟩ := hY
  obtain ⟨hWcont, hWne, -⟩ := hW φ (hYmir φ hφY)
  obtain ⟨g, hg⟩ := hWne hφ0
  obtain ⟨g₀, harch, hloc, hsupp⟩ := hreg S g
  have hg₀ : PositivityTheory.jumpWindows.Wh ψ φ g₀ ≠ 0 := by
    intro h0
    refine hg (hWV E a S _ hWcont ?_ g g₀ harch hloc hsupp h0)
    intro w hw h hh h0' u
    obtain ⟨B, hB⟩ := hφeig w hw
    exact hWS E a ψ hψ w (hS w hw) B φ (hYmir φ hφY) hB h hh h0' u
  have hφ'Y : PositivityTheory.jumpWindows.Rt E a g₀ φ ∈ Y := hYtr g₀ hsupp φ hφY
  have hW1 : PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1 ≠ 0 := by
    rw [htr, one_mul]
    exact hg₀
  refine ⟨(PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1)⁻¹ •
      PositivityTheory.jumpWindows.Rt E a g₀ φ, Y.smul_mem _ hφ'Y, ?_, ?_, ?_⟩
  · exact PositivityTheory.jumpWindows.SmoothVectorOrbit.smV_smul _ _ _ (hsmooth g₀ φ hφsm)
  · exact hsph_smul _ _ (hsph g₀ φ hφsph)
  · obtain ⟨Λ, hΛ1⟩ := hΛ 1
    rw [← hΛ1 _ (hYmir _ (Y.smul_mem _ hφ'Y)), map_smul, hΛ1 _ (hYmir _ hφ'Y), smul_eq_mul,
      inv_mul_cancel₀ hW1]

end PositivityTheory.jumpWindows

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AdelicCharacterCondition

theorem isCharAF_of {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF E ψ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  have hb : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime, hb⟩
  exact ⟨hψ.cont, hψ.norm, hψ.rat, _, hy⟩

theorem condAA {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    ∀ᶠ v in (cofinite : Filter (HeightOneSpectrum (𝓞 E))), ∀ t : v.adicCompletion E,
      (∀ s ∈ v.adicCompletionIntegers E, ψ (sFin E (sLoc E v (s * t))) = 1) ↔ t ∈ v.adicCompletionIntegers E := by
  have h := _root_.PI.VolStabSW.VolAAW.condAA_of (_root_.PI.VolStabSW.VolAAW.condExact_of _root_.PI.VolStabSW.sAf_holds
    (_root_.PI.VolStabSW.chInf_of_lift _root_.PI.VolStabSW.chLift_holds)) E ψ (isCharAF_of hψ)
  filter_upwards [h] with v hv t
  simp only [sFin_sLoc_eq]
  exact hv t

end AdelicCharacterCondition

theorem adelic_character_holds : StandardCharacterExists := by
  intro E _ _ _
  obtain ⟨ψ, hψ⟩ := exists_stdPsi E
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [AdelicCharacterCondition.condAA hψ] with w hw
  have hint : ∀ y ∈ Ov E w, ψ (sFin E (sLoc E w y)) = 1 := by
    intro y hy
    have := (hw 1).2 (one_mem _) y hy
    rwa [mul_one] at this
  refine ⟨hint, ?_⟩
  set ϖ := _root_.PI.VolStabSW.unifV w with hϖ
  have hϖ0 : ϖ ≠ 0 := (_root_.PI.VolStabSW.unifV_spec w).1
  have hu : IsUnifV E w ϖ := _root_.PI.VolStabSW.unifV_val w
  have hnot : ϖ⁻¹ ∉ w.adicCompletionIntegers E := by
    intro h
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := _root_.PI.VolStabSW.unifV_val w
    rw [hv] at h
    exact absurd h (by decide)
  have hex : ¬ ∀ s ∈ w.adicCompletionIntegers E, ψ (sFin E (sLoc E w (s * ϖ⁻¹))) = 1 :=
    fun h => hnot ((hw _).1 h)
  push Not at hex
  obtain ⟨s, hs, hne⟩ := hex
  refine ⟨ϖ, s * ϖ⁻¹, hu, ?_, hne⟩
  rw [mul_comm s, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  exact hs

end PositivityTheory.jumpWindows

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearInduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem step (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hma : m + 1 < a) (hG : Good ψ (m + 1) f)
    (Z : Set (GA E a)) (hZ : ∀ γ, IsMir (m + 1) γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z)
    (hc : ∀ g ∈ Z, colT ψ (m + 1) f g = 0) : ∀ g ∈ Z, f g = 0 := by
  intro g₀ hg
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) = 0 := by
    refine _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer fun ξ => ?_
    by_cases hξ0 : ξ = 0
    · subst hξ0
      have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
      have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
          ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
        intro x
        simp [dot]
      simp only [e, one_mul]
      exact hv
    · obtain ⟨γ, hγ, hγξ⟩ := _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
      have h1 := hc _ (hZ γ hγ g₀ hg)
      simp only [colT] at h1
      rw [_root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
      have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) =>
          ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ := funext hγξ
      rw [e] at h1
      exact h1
  have h1 := congrFun hΦ 0
  simp only [Pi.zero_apply] at h1
  have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
  rw [e, one_mul] at h1
  exact h1

theorem main (hψ : StdPsi ψ) (m : ℕ) : ∀ (f : GA E a → ℂ), (m < a ∨ m = 0) → Good ψ m f →
    ∀ Z : Set (GA E a), (∀ γ, IsMir m γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z) →
      (∀ g ∈ Z, whit ψ m f g = 0) → ∀ g ∈ Z, f g = 0 := by
  induction m with
  | zero => intro f _ _ Z _ hw; exact hw
  | succ m ih =>
    intro f hm hG Z hZ hw
    have hma : m + 1 < a := by omega
    refine step hψ m f hma hG Z hZ ?_
    refine ih _ (Or.inl (by omega)) (_root_.GlobalTheory.CuspRep.Generic.good_colT hψ hma hG) Z
      (fun γ hγ g hg => hZ γ (fun i k h => hγ i k (by omega)) g hg) ?_
    intro g hg
    exact hw g hg

end GeneralLinearInduction

theorem induction_g11_holds : FourierUniquenessMirabolic := by
  intro E _ _ _ a ψ hψ m f hm hG Z hZ _ hw
  exact GeneralLinearInduction.main hψ m f hm hG Z hZ hw

end PositivityTheory.jumpWindows

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace MirrorMap

theorem mir_map {R S : Type} [CommRing R] [CommRing S] {a m : ℕ} (p : R →+* S) {γ : GL (Fin a) R}
    (h : Mir m γ) : Mir m (GeneralLinearGroup.map p γ) := by
  intro i k hik
  change p (γ.val i k) = _
  rw [h i k hik, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mirS_mul (h10 : MirabolicColumnBlock) {S : Finset (Pl E)} {x g : GA E a} (hx : Mir (a - 1) x) (hg : MirS S g) :
    MirS S (x * g) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map (pInf E) hx) hg.1
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map ((pLoc E w).comp (pFin E)) hx) (hg.2 w hw)

end MirrorMap

theorem mirror_global_of : MirabolicColumnBlock → G0 → G5 → G9 → PlacewiseToOutsideS → FourierUniquenessMirabolic → WeakApproximationGL → WhittakerVanishingImpliesZero := by
  intro h10 h0 h5 h9 h9b h11 h12 E _ _ _ a ψ hψ S hcond φ hgood hleft hsat hvan
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hproj, -⟩ := h0 E a
  have hcont : Continuous (Wh ψ φ) := ((h5 E a ψ hψ).2.2.2 φ hgood).1
  have step1 : ∀ g, MirS S g → Wh ψ φ g = 0 := by
    intro g hg
    obtain ⟨g₀, e1, e2, e3⟩ := hproj S g
    refine h9b E a S (Wh ψ φ) hcont ?_ g g₀ e1 e2 e3 ?_
    · intro w hw h hh hz u
      obtain ⟨B, hB⟩ := hsat w hw
      exact h9 E a ψ hψ w (hcond w hw) B φ hgood hB h hh hz u
    · refine hvan g₀ ⟨?_, fun w hw => ?_⟩ e3
      · rw [e1]; exact hg.1
      · rw [e2 w hw]; exact hg.2 w hw
  have step2 : ∀ g, MirS S g → φ g = 0 := by
    intro g hg
    refine h11 E a ψ hψ (a - 1) φ (by omega) hgood {g | MirS S g} ?_ ?_ step1 g hg
    · intro γ hγ g hg
      exact MirrorMap.mirS_mul h10 (MirrorMap.mir_map (algebraMap E (Ad E)) hγ) hg
    · intro k hk y g hg
      exact MirrorMap.mirS_mul h10 ((h10 (Ad E) a (a - 1)).2.2.2.2.2.1 k y hk) hg
  have hEq : (⇑φ) = fun _ => (0 : ℂ) := by
    refine Continuous.ext_on (h12 E a S) φ.continuous continuous_const ?_
    rintro x ⟨γ, g, rfl, hg1, hg2⟩
    show φ (ratGL E a γ * g) = 0
    rw [hleft]
    refine step2 g ⟨?_, fun w hw => ?_⟩
    · rw [hg1]; exact (h10 _ a (a - 1)).2.2.1
    · rw [hg2 w hw]; exact (h10 _ a (a - 1)).2.2.1
  ext x
  simpa using congrFun hEq x

end PositivityTheory.jumpWindows

end
end

section
namespace PositivityTheory.jumpWindows

theorem meet_of : S2 → MirabolicColumnBlock → G0 → G1 → AlmostEverywhereSpherical → G2a → G2b → G2c → G5 → G5b → FourierInductionSteps → G8 → StandardCharacterExists → WhittakerVanishingImpliesZero → Meet :=
  GlobalTheory.CompanionTheory.ClosedInvariantMeet.meet_of_steps

end PositivityTheory.jumpWindows
end

section
namespace PositivityTheory.jumpWindows

theorem finite_part_of_meet : Meet → CuspidalIrreducibleSubrep :=
  GlobalTheory.CompanionTheory.FinitePart.g14_of_meet

end PositivityTheory.jumpWindows
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

theorem smonorm_of : Meet → CuspidalIrreducibleSubrep → SmoNorm := by
  intro hM hG E _ _ _ a π π' hπ hπ' hS
  let μ : Measure (GA E a) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨H, hH, hf⟩ := hG E a μ π hπ
  obtain ⟨H', hH', hf'⟩ := hG E a μ π' hπ'
  have hne : H ⊓ H' ≠ ⊥ := hM E a μ π π' H H' hπ hπ' hH.1 hH'.1
    (fun φ hφ => ⟨hf.finitePartMemL2 φ hφ, hf.classes_le (toL2_mem_classes hφ (hf.finitePartMemL2 φ hφ))⟩)
    (fun φ hφ => ⟨hf'.finitePartMemL2 φ hφ, hf'.classes_le (toL2_mem_classes hφ (hf'.finitePartMemL2 φ hφ))⟩) hS
  have h1 : H ⊓ H' = H := (hH.2.2 _ inf_le_left (hH.1.inf hH'.1)).resolve_left hne
  have h2 : H ⊓ H' = H' := (hH'.2.2 _ inf_le_right (hH.1.inf hH'.1)).resolve_left hne
  have e : H = H' := h1.symm.trans h2
  subst e
  exact hf.unique hf'

end PositivityTheory.jumpWindows

end
end

section
open GlobalTheory.CuspRep

namespace PositivityTheory.jumpWindows

theorem mean_convergence_of : Smo → GlobalTheory.Published.CuspidalMultiplicityOne := by
  intro h E _ _ _ a π π' e
  refine congrArg CuspSub.V (h E a π π' ?_)
  filter_upwards [GlobalTheory.T.cuspidal_GL_local_components_eventually_satake CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π] with w hw
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, hB, e ▸ (show (CG.mk π).HasSat w B from hB)⟩

end PositivityTheory.jumpWindows
end

section
namespace PositivityTheory.jumpWindows

theorem compositionalInverseSymm : S1 :=
  lie_algebra_action_exists

theorem orthogonalSplitPolarizationVanishes : S2 :=
  smooth_vectors_stable_intertwiner

theorem addPreservesExpCongruence : S3 :=
  unit_chart_operator_bound compositionalInverseSymm

theorem expCongruenceExtendsToSum : S4 :=
  valuation_bound_of_three

theorem hit_valuation_bound : S5 :=
  haar_measure_pairing

theorem smooth_vectors_conjugation_holds : S6 :=
  conjugation_units_open orthogonalSplitPolarizationVanishes expCongruenceExtendsToSum

theorem exists_logarithm_linear_holds : S8 :=
  exists_logarithm_linear

theorem positive_matrix_block_product_holds : MirabolicColumnBlock :=
  positive_matrix_block_product

theorem mirabolic_induction_step_holds : S7 :=
  mirabolic_induction_step_exists orthogonalSplitPolarizationVanishes addPreservesExpCongruence hit_valuation_bound smooth_vectors_conjugation_holds exists_logarithm_linear_holds positive_matrix_block_product_holds

theorem lattice_open_last_entry_holds : S9 :=
  lattice_open_last_entry positive_matrix_block_product_holds

theorem automorphic_basic_setup_holds : G0 :=
  standard_stabiliser_bound

theorem multiplicity_one_holds : G1 :=
  firstGeometricCondition_of_properties compositionalInverseSymm

theorem almost_everywhere_spherical : AlmostEverywhereSpherical :=
  almost_everywhere_spherical_of_G1 multiplicity_one_holds

theorem averaging_projection_linear_holds : G2a :=
  averaging_projection_linear

theorem bounded_invariant_L2_holds : G2b :=
  bounded_invariant_functions_in_L2

theorem hecke_operator_automorphic_holds : G2c :=
  hecke_operator_of_automorphic automorphic_basic_setup_holds

theorem whittaker_functional_exists_holds : G5 :=
  local_group_averaging_tensor

theorem smooth_vectors_regular_holds : G5b :=
  smooth_vectors_regular_representation orthogonalSplitPolarizationVanishes automorphic_basic_setup_holds

theorem whittaker_nondegenerate_holds : G6 :=
  whittaker_nondegenerate_character mirabolic_induction_step_holds positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds

theorem whittaker_expansion_cuspidal_holds : G7 :=
  whittaker_expansion_cuspidal orthogonalSplitPolarizationVanishes lattice_open_last_entry_holds positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds smooth_vectors_regular_holds

theorem whittaker_factorization_places_holds : FourierInductionSteps :=
  whittaker_factorization_places whittaker_nondegenerate_holds whittaker_expansion_cuspidal_holds

theorem whittaker_uniqueness_local_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : G9 :=
  whittaker_uniqueness_local h7 h12 automorphic_basic_setup_holds whittaker_functional_exists_holds

theorem convergence_entries_general_linear_holds : PlacewiseToOutsideS :=
  convergence_entries_general_linear automorphic_basic_setup_holds

theorem smooth_vector_orbit_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : G8 :=
  smooth_vector_orbit_invariance automorphic_basic_setup_holds whittaker_functional_exists_holds smooth_vectors_regular_holds (whittaker_uniqueness_local_holds h7 h12) convergence_entries_general_linear_holds

theorem adelic_character_condition_holds : StandardCharacterExists :=
  adelic_character_holds

theorem local_uniqueness_auxiliary_holds : FourierUniquenessMirabolic :=
  induction_g11_holds

theorem good_inverse_dense_range_holds : WeakApproximationGL :=
  good_inverse_of_G0 automorphic_basic_setup_holds

theorem whittaker_support_theorem_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : WhittakerVanishingImpliesZero :=
  mirror_global_of positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds (whittaker_uniqueness_local_holds h7 h12) convergence_entries_general_linear_holds local_uniqueness_auxiliary_holds good_inverse_dense_range_holds

theorem finite_part_meets_conditions (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : Meet :=
  meet_of orthogonalSplitPolarizationVanishes positive_matrix_block_product_holds automorphic_basic_setup_holds multiplicity_one_holds almost_everywhere_spherical averaging_projection_linear_holds bounded_invariant_L2_holds hecke_operator_automorphic_holds whittaker_functional_exists_holds smooth_vectors_regular_holds whittaker_factorization_places_holds (smooth_vector_orbit_holds h7 h12) adelic_character_condition_holds (whittaker_support_theorem_holds h7 h12)

theorem finite_part_of_meet_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : CuspidalIrreducibleSubrep :=
  finite_part_of_meet (finite_part_meets_conditions h7 h12)

theorem smooth_multiplicity_normalized (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : SmoNorm :=
  smonorm_of (finite_part_meets_conditions h7 h12) (finite_part_of_meet_holds h7 h12)

theorem finite_infinite_product_one_holds : HeckeCharacterRigidity :=
  finite_infinite_product_eq_one

theorem smooth_multiplicity_one_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : Smo :=
  smo_of (smooth_multiplicity_normalized h7 h12) finite_infinite_product_one_holds

theorem cuspidal_multiplicity_one (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : GlobalTheory.Published.CuspidalMultiplicityOne :=
  mean_convergence_of (smooth_multiplicity_one_holds h7 h12)

end PositivityTheory.jumpWindows
end
