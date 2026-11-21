import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstance
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import BuildAid.ForwardExisting
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LocalPointData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔ x ∈ (Formalism.IndefR.Eqv.UI.instV fr).GFset) ∧ (∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) ∧ ∀ W, (Formalism.IndefR.Eqv.UI.instV fr).IsIsot W → ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ NI V C₀ → x ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W := by
  first | exact @GlobalTheory.BridgeDict.bridge_dict | exact GlobalTheory.BridgeDict.bridge_dict | (intros; apply GlobalTheory.BridgeDict.bridge_dict <;> assumption)
end

section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_integralBasis_covolume_constant : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ), 0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  first | exact @GlobalTheory.CuspGeo.covolume_const | exact GlobalTheory.CuspGeo.covolume_const | (intros; apply GlobalTheory.CuspGeo.covolume_const <;> assumption)
end

section
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo

theorem exists_integralMatrix_of_same_multiplicationMatrices {E : Type*} [Field E] [NumberField E] {n N : ℕ}
    (e e₀ : Fin N → Fin n → E) (hli : LinearIndependent ℤ e)
    (he : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i)
    (he₀ : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e₀ i)
    (h : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis E k : E) • e j = ∑ i, z i • e i → (integralBasis E k : E) • e₀ j = ∑ i, z i • e₀ i) :
    ∃ M : Matrix (Fin n) (Fin n) E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  classical
  let A : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e
  let B : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e₀
  have hA : ∀ z, A z = ∑ i, z i • e i := fun z => Fintype.linearCombination_apply ℤ e z
  have hB : ∀ z, B z = ∑ i, z i • e₀ i := fun z => Fintype.linearCombination_apply ℤ e₀ z
  have hAs : ∀ j, A (Pi.single j 1) = e j := fun j => by simp [A]
  have hBs : ∀ j, B (Pi.single j 1) = e₀ j := fun j => by simp [B]
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun z hz => ?_
    rw [hA] at hz
    exact funext (Fintype.linearIndependent_iff.1 hli z hz)
  have heint : ∀ j i, IsIntegral ℤ (e j i) := fun j => (he _).2 ⟨Pi.single j 1, by rw [← hA, hAs]⟩
  let S : Submodule ℤ ((Fin n → E) × (Fin n → E)) := LinearMap.range (A.prod B)
  have hk : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (z : Fin N → ℤ),
      (integralBasis E k : E) • (A z, B z) ∈ S := by
    intro k z
    have h1 : (integralBasis E k : E) • (A z, B z)
        = ∑ j, z j • ((integralBasis E k : E) • (e j, e₀ j)) := by
      have h0 : (A z, B z) = ∑ j, z j • (e j, e₀ j) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]; exact hA z
        · rw [Prod.snd_sum]; exact hB z
      rw [h0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm (z j)]
    rw [h1]
    refine S.sum_mem fun j _ => S.smul_mem _ ?_
    have hint : ∀ i, IsIntegral ℤ (((integralBasis E k : E) • e j) i) := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (heint j i)
    obtain ⟨w, hw⟩ := (he _).1 hint
    refine ⟨w, ?_⟩
    have hw₀ := h k j w hw
    rw [← hA] at hw
    rw [← hB] at hw₀
    exact Prod.ext hw.symm hw₀.symm
  have ha : ∀ a : E, IsIntegral ℤ a → ∀ z : Fin N → ℤ, a • (A z, B z) ∈ S := by
    intro a hai z
    let a' : 𝓞 E := ⟨a, hai⟩
    have h1 : a = ∑ k, (RingOfIntegers.basis E).repr a' k • (integralBasis E k : E) := by
      have h2 := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr a')
      rw [map_sum] at h2
      simp only [map_zsmul] at h2
      simp only [integralBasis_apply]
      exact h2.symm
    rw [h1, Finset.sum_smul]
    refine S.sum_mem fun k _ => ?_
    rw [smul_assoc]
    exact S.smul_mem _ (hk k z)
  have hu : ∀ j : Fin n, ∃ z : Fin N → ℤ, (Pi.single j 1 : Fin n → E) = A z := fun j => by
    obtain ⟨z, hz⟩ := (he (Pi.single j 1)).1 fun i => by
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    exact ⟨z, by rw [hA]; exact hz⟩
  choose c hc using hu
  refine ⟨Matrix.of fun i j => B (c j) i, fun i j => (he₀ _).2 ⟨c j, hB _⟩ i, fun l => ?_⟩
  have hs : ∑ j, e l j • (A (c j), B (c j)) ∈ S := S.sum_mem fun j _ => ha _ (heint l j) _
  obtain ⟨w, hw⟩ := hs
  have hw1 : A w = e l := by
    have h1 := congrArg Prod.fst hw
    rw [Prod.fst_sum] at h1
    simp only [Prod.smul_mk, ← hc] at h1
    refine Eq.trans h1 ?_
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hw2 : B w = ∑ j, e l j • B (c j) := by
    have h1 := congrArg Prod.snd hw
    rw [Prod.snd_sum] at h1
    exact h1
  have hw3 : w = Pi.single l 1 := hAinj (by rw [hw1, hAs])
  rw [← hBs, ← hw3, hw2]
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem exists_integral_matrix_of_same_mul : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E),
    IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j :=
  fun _ _ e e₀ he he₀ h => exists_integralMatrix_of_same_multiplicationMatrices e e₀ he.1 he.2 he₀.2 h

end GlobalTheory.CuspGeo
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E), IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  atlas_forward_decl GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul
end

section
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo.TraceUnitary

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def trBil (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ[ℚ] (Fin n → E) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (Formalism.UG.hform σ J x y))
    (fun x x' y => by
      rw [← map_add]; congr 1
      simp [Formalism.UG.hform, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp [Formalism.UG.hform, Finset.smul_sum, Rat.smul_def, mul_assoc])
    (fun x y y' => by
      rw [← map_add]; congr 1
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp only [Formalism.UG.hform, Finset.smul_sum, Rat.smul_def, Pi.smul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem trBil_apply (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    trBil σ J x y = Algebra.trace ℚ E (Formalism.UG.hform σ J x y) := rfl

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (a : E) :
    Formalism.UG.hform σ J x (a • y) = a * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem span_eq_top {N : ℕ} (e : Fin N → Fin n → E)
    (h : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) → ∃ z : Fin N → ℤ, u = ∑ i, z i • e i) :
    Submodule.span ℚ (Set.range e) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro u _
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image u)
  obtain ⟨z, hz⟩ := h (d • u) (fun i => hint (u i) (Finset.mem_image_of_mem u (Finset.mem_univ i)))
  have h1 : (d : ℚ) • u ∈ Submodule.span ℚ (Set.range e) := by
    rw [Int.cast_smul_eq_zsmul, hz]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  exact (Submodule.smul_mem_iff _ hd').1 h1

theorem unitary_of_trace (σ : E →+* E) (J M : Matrix (Fin n) (Fin n) E) {N : ℕ} (e : Fin N → Fin n → E)
    (hs : Submodule.span ℚ (Set.range e) = ⊤)
    (h : ∀ i j, trBil σ J (M *ᵥ e i) (M *ᵥ e j) = trBil σ J (e i) (e j)) :
    Formalism.UG.cT σ M * J * M = J := by
  classical
  let f : (Fin n → E) →ₗ[ℚ] (Fin n → E) := (Matrix.mulVecLin M).restrictScalars ℚ
  have hB : (trBil σ J).compl₁₂ f f = trBil σ J := by
    refine LinearMap.ext_on_range hs fun i => LinearMap.ext_on_range hs fun j => ?_
    simpa [f] using h i j
  have hB' : ∀ x y, trBil σ J (M *ᵥ x) (M *ᵥ y) = trBil σ J x y := fun x y => by
    have := LinearMap.congr_fun₂ hB x y
    simpa [f] using this
  have hh : ∀ x y, Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := fun x y => by
    by_contra hne
    have hD : Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) - Formalism.UG.hform σ J x y ≠ 0 := sub_ne_zero.2 hne
    have h1 := hB' x ((Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) - Formalism.UG.hform σ J x y)⁻¹ • y)
    rw [Matrix.mulVec_smul, trBil_apply, trBil_apply, hform_smul_right, hform_smul_right, ← sub_eq_zero,
      ← map_sub, ← mul_sub, inv_mul_cancel₀ hD, ← (algebraMap ℚ E).map_one, Algebra.trace_algebraMap] at h1
    have : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
    simp [this] at h1
  ext i j
  have := hh (Pi.single i 1) (Pi.single j 1)
  simp only [Formalism.UG.hform, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, this]
  simp [apply_ite σ]

end GlobalTheory.CuspGeo.TraceUnitary

namespace GlobalTheory.CuspGeo

theorem unitary_of_trForm_zBasis (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E)
    (M : Matrix (Fin I.n) (Fin I.n) I.E) (he : IsZBasis I e)
    (h : ∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) :
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J :=
  TraceUnitary.unitary_of_trace _ _ _ e (TraceUnitary.span_eq_top e fun u hu => (he.2 u).1 hu) h

end GlobalTheory.CuspGeo

end
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis : ∀ (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin I.n) (Fin I.n) I.E), IsZBasis I e →
    (∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) →
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J := by
  atlas_forward_decl GlobalTheory.CuspGeo.unitary_of_trForm_zBasis
end

section
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.BasesFin

theorem trForm_denom : ∀ (I : AutInst), ∃ c : ℕ, 0 < c ∧ ∀ x y : Fin I.n → I.E, IntVec I x → IntVec I y →
    ∃ m : ℤ, (c : ℚ) * trForm I x y = m := by
  intro I
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  have hcJ : ∀ a b, IsIntegral ℤ ((y.natAbs : I.E) * I.J a b) := by
    intro a b
    have h := hyi (I.J a b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with hy | hy
    · rw [hy] at h; simpa using h
    · rw [hy] at h
      have := h.neg
      simpa [neg_mul] using this
  intro x z hx hz
  have hint : IsIntegral ℤ ((y.natAbs : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x z) := by
    unfold Formalism.UG.hform
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have : (y.natAbs : I.E) * ((starRingEnd I.E) (x i) * I.J i j * z j)
        = (starRingEnd I.E) (x i) * ((y.natAbs : I.E) * I.J i j) * z j := by ring
    rw [this]
    have hs : IsIntegral ℤ ((starRingEnd I.E) (x i)) := (hx i).map (starRingEnd I.E).toIntAlgHom
    exact (hs.mul (hcJ i j)).mul (hz j)
  have htr := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) hint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨m, ?_⟩
  rw [eq_intCast] at hm
  rw [hm]
  unfold trForm
  rw [← map_natCast (algebraMap ℚ I.E), ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem fix_one (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I.n) I.E)
    (he : IsZBasis I e) (hA : ∀ j, A *ᵥ e j = e j) : A = 1 := by
  have key : ∀ u, IntVec I u → A *ᵥ u = u := by
    intro u hu
    obtain ⟨z, rfl⟩ := (he.2 u).1 hu
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hA]
  ext i j
  have hs : IntVec I (Pi.single j 1) := by
    intro l
    by_cases h : l = j
    · subst h; simpa using isIntegral_one
    · simp [Pi.single_apply, h, isIntegral_zero]
  have := congrFun (key _ hs) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem bases_finite_classes : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  intro I N R
  classical
  obtain ⟨c, hc0, hc⟩ := trForm_denom I
  let T := (Module.Free.ChooseBasisIndex ℤ (𝓞 I.E) → Fin N → Fin N → ℤ) × (Fin N → Fin N → ℚ)
  let has : (Fin N → Fin I.n → I.E) → T → Prop := fun e t =>
    (∀ k j, (integralBasis I.E k : I.E) • e j = ∑ i, t.1 k j i • e i) ∧ ∀ i j, trForm I (e i) (e j) = t.2 i j
  let A : Set T := (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => {z : ℤ | |(z:ℝ)| ≤ R}) ×ˢ
    (Set.univ.pi fun _ => Set.univ.pi fun _ => {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m})
  have hZ : {z : ℤ | |(z:ℝ)| ≤ R}.Finite := by
    refine (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz => ?_
    simp only [Set.mem_setOf_eq] at hz
    have h := abs_le.mp hz
    have hR := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉:ℝ)) ≤ z := by linarith
      exact_mod_cast this
    · have : (z:ℝ) ≤ ⌈R⌉ := by linarith
      exact_mod_cast this
  have hQ : {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m}.Finite := by
    refine ((Set.finite_Icc (-⌈R * c⌉) ⌈R * c⌉).image fun m : ℤ => (m : ℚ) / c).subset ?_
    rintro q ⟨hq, m, hm⟩
    have hcpos : (0:ℝ) < c := by exact_mod_cast hc0
    have hmq : (m:ℝ) = c * q := by exact_mod_cast hm.symm
    have h := abs_le.mp hq
    have hR := Int.le_ceil (R * c)
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · have : (-(⌈R*c⌉:ℝ)) ≤ m := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have : (m:ℝ) ≤ ⌈R*c⌉ := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have hc' : (c:ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
      simp only
      rw [← hm]; field_simp
  have hA : A.Finite := (Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hZ).prod
    (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hQ)
  let pick : T → (Fin N → Fin I.n → I.E) := fun t =>
    if h : ∃ e, IsZBasis I e ∧ has e t then Classical.choose h else 0
  have hpick : ∀ t (h : ∃ e, IsZBasis I e ∧ has e t), IsZBasis I (pick t) ∧ has (pick t) t := by
    intro t h
    simp only [pick, dif_pos h]
    exact Classical.choose_spec h
  have uniq : ∀ (f : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → ∀ k j (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → w = t.1 k j := by
    intro f t hf hft k j w hw
    rw [hft.1 k j] at hw
    have h0 : ∑ i, (w i - t.1 k j i) • f i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hw, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf.1 _ h0 i)
  have compat : ∀ (f g : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → has g t →
      ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → (integralBasis I.E k : I.E) • g j = ∑ i, w i • g i := by
    intro f g t hf hft hgt k j w hw
    rw [uniq f t hf hft k j w hw]
    exact hgt.1 k j
  refine ⟨pick '' {t ∈ A | ∃ e, IsZBasis I e ∧ has e t}, (hA.subset (Set.sep_subset _ _)).image _, ?_, ?_⟩
  · rintro _ ⟨t, ⟨-, h⟩, rfl⟩
    exact (hpick t h).1
  · intro e he hb
    choose z hz hzb using hb.1
    let t : T := (z, fun i j => trForm I (e i) (e j))
    have ht : has e t := ⟨hz, fun i j => rfl⟩
    have hint : ∀ i, IntVec I (e i) := fun i => (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
    have htA : t ∈ A := ⟨fun k _ j _ i _ => hzb k j i, fun i _ j _ => ⟨hb.2 i j, hc _ _ (hint i) (hint j)⟩⟩
    have hex : ∃ e', IsZBasis I e' ∧ has e' t := ⟨e, he, ht⟩
    obtain ⟨he₀, ht₀⟩ := hpick t hex
    obtain ⟨M, hMi, hMe⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I e (pick t) he he₀ (compat e (pick t) t he ht ht₀)
    obtain ⟨M', hM'i, hM'e⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I (pick t) e he₀ he (compat (pick t) e t he₀ ht₀ ht)
    have h1 : M' * M = 1 := fix_one I e _ he fun j => by rw [← Matrix.mulVec_mulVec, hMe, hM'e]
    have h2 : M * M' = 1 := (mul_eq_one_comm_of_card_eq (Fin I.n) (Fin I.n) I.E rfl).mp h1
    let γ : GL (Fin I.n) I.E := ⟨M, M', h2, h1⟩
    refine ⟨pick t, ⟨t, ⟨htA, hex⟩, rfl⟩, γ, ?_, hMi, hM'i, hMe⟩
    show Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J
    exact GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis I e M he fun i j => by rw [hMe, hMe]; exact ht₀.2 i j

end GlobalTheory.BasesFin
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  atlas_forward_decl GlobalTheory.BasesFin.bases_finite_classes
end

section
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.IntUnitCpt

open Formalism.MainNotions.LeviCoordinates

open Classical in

def red {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) (A : Matrix (Fin n) (Fin n) E) :
    Fin n → Fin n → (𝓞 E ⧸ Ideal.span {(M : 𝓞 E)}) := fun i j =>
  if h : IsIntegral ℤ (A i j) then Ideal.Quotient.mk _ ⟨A i j, h⟩ else 0

theorem sub_of_red {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ i j, IsIntegral ℤ (A i j)) (hB : ∀ i j, IsIntegral ℤ (B i j)) (h : red M A = red M B) :
    ∀ i j, ∃ b : E, IsIntegral ℤ b ∧ (A - B) i j = (M : E) * b := by
  intro i j
  have e := congrFun (congrFun h i) j
  simp only [red, dif_pos (hA i j), dif_pos (hB i j)] at e
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
  clear e
  refine ⟨b, RingOfIntegers.isIntegral_coe b, ?_⟩
  have := congrArg (fun z : 𝓞 E => (z : E)) hb
  simp only [map_mul, map_natCast, map_sub] at this
  rw [Matrix.sub_apply, mul_comm]
  exact this.symm

theorem mul_cong {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) {C D : Matrix (Fin n) (Fin n) E}
    (hC : ∀ i j, IsIntegral ℤ (C i j)) (hD : ∀ i j, ∃ b : E, IsIntegral ℤ b ∧ D i j = (M : E) * b) :
    ∀ i j, ∃ a : E, IsIntegral ℤ a ∧ (C * D) i j = (M : E) * a := by
  intro i j
  choose b hb hb' using hD
  refine ⟨∑ k, C i k * b k j, IsIntegral.sum _ fun k _ => (hC i k).mul (hb k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hb' k j]; ring

theorem kset_nhds (I : AutInst) : I.Kset ∈ 𝓝 (1 : I.Gf) := by
  have ho := I.topf_open 1 le_rfl
  refine Filter.mem_of_superset (ho.mem_nhds ?_) fun x hx => hx.1
  refine ⟨(Formalism.UG.stabGL _).one_mem, fun y hy => ⟨0, Submodule.zero_mem _, by simp⟩⟩

end GlobalTheory.IntUnitCpt

namespace GlobalTheory.IntUnitCpt

def fp (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : I.Gf :=
  ⟨Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ,
    Formalism.UG.Final.RatPtsLe I.F I.E (Fin I.n) I.cm.sig I.J (Af I.F) (Subgroup.mem_map_of_mem _ hγ)⟩

theorem fp_mul (I : AutInst) {γ δ : GL (Fin I.n) I.E} (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (hδ : δ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    fp I (γ⁻¹ * δ) (mul_mem (inv_mem hγ) hδ) = (fp I γ hγ)⁻¹ * fp I δ hδ := by
  apply Subtype.ext
  simp [fp, map_mul, map_inv]

theorem eq_of_real (I : AutInst) (v : InfinitePlace I.F) {A B : Matrix (Fin I.n) (Fin I.n) I.E}
    (h : (I.P v)⁻¹ * A.map (I.φ v) * I.P v = (I.P v)⁻¹ * B.map (I.φ v) * I.P v) : A = B := by
  have h2 : A.map (I.φ v) = B.map (I.φ v) := by
    have := congrArg (fun X => I.P v * X * (I.P v)⁻¹) h
    have hp := Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv I v
    simp only [← Matrix.mul_assoc, hp, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, hp, Matrix.mul_one] using this
  ext i j
  exact (I.φ v).injective (congrFun (congrFun h2 i) j)

end GlobalTheory.IntUnitCpt

namespace GlobalTheory.IntUnitCpt

theorem intUnit_compact : ∀ I : AutInst, ∃ K : Set I.Gf, IsCompact K ∧ ∀ γ : GL (Fin I.n) I.E,
    γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) →
    (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) →
    ∃ x ∈ I.GFset, x.2 ∈ K ∧ ∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
  intro I
  classical
  obtain ⟨M, hM, hcong⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I I.Kset (kset_nhds I)
  let T : Set (GL (Fin I.n) I.E) := {γ | γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧
    ∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)}
  haveI : Finite (𝓞 I.E ⧸ Ideal.span {(M : 𝓞 I.E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Nat.one_le_iff_ne_zero.1 hM))
  let Kq : (Fin I.n → Fin I.n → (𝓞 I.E ⧸ Ideal.span {(M : 𝓞 I.E)})) → Set I.Gf := fun q =>
    if h : ∃ γ, γ ∈ T ∧ red M (γ : Matrix (Fin I.n) (Fin I.n) I.E) = q then
      (fun k => fp I h.choose h.choose_spec.1.1 * k) '' I.Kset else ∅
  refine ⟨⋃ q, Kq q, isCompact_iUnion fun q => ?_, fun γ hγ hi hi' => ?_⟩
  · simp only [Kq]
    split_ifs
    · exact (Formalism.L2.SG.Closed.AutKCompact_holds I).image (continuous_const_mul _)
    · exact isCompact_empty
  · have hex : ∃ γ', γ' ∈ T ∧ red M (γ' : Matrix (Fin I.n) (Fin I.n) I.E) = red M (γ : Matrix (Fin I.n) (Fin I.n) I.E) :=
      ⟨γ, ⟨hγ, hi, hi'⟩, rfl⟩
    refine ⟨(fun v => Formalism.L2.S.S7.DensRat.ratReal I γ hγ v, fp I γ hγ), ⟨γ, hγ, fun v => rfl, rfl⟩,
      Set.mem_iUnion.2 ⟨red M (γ : Matrix (Fin I.n) (Fin I.n) I.E), ?_⟩, fun v => rfl⟩
    simp only [Kq, dif_pos hex]
    obtain ⟨hT', hr⟩ := hex.choose_spec
    set γ' := hex.choose with hγ'def
    refine ⟨(fp I γ' hT'.1)⁻¹ * fp I γ hγ, ?_, mul_inv_cancel_left _ _⟩
    have hδ : γ'⁻¹ * γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := mul_mem (inv_mem hT'.1) hγ
    have hsub := sub_of_red M hT'.2.1 hi hr
    have c1 : CompanionTheory.D.gk.RF.Cong I M ((γ'⁻¹ * γ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) := by
      have e : ((γ'⁻¹ * γ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) - 1 =
          ((γ'⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *
            ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - (γ' : Matrix (Fin I.n) (Fin I.n) I.E)) := by
        rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul γ'⁻¹ γ', inv_mul_cancel, Units.val_one]
      intro i j
      rw [e]
      refine mul_cong M hT'.2.2 (fun k l => ?_) i j
      obtain ⟨b, hb, hb'⟩ := hsub k l
      exact ⟨-b, hb.neg, by rw [Matrix.sub_apply] at hb' ⊢; rw [← neg_sub, hb']; ring⟩
    have c2 : CompanionTheory.D.gk.RF.Cong I M (((γ'⁻¹ * γ)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) := by
      have e : (((γ'⁻¹ * γ)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) - 1 =
          ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *
            ((γ' : Matrix (Fin I.n) (Fin I.n) I.E) - (γ : Matrix (Fin I.n) (Fin I.n) I.E)) := by
        rw [_root_.mul_inv_rev, inv_inv, Matrix.mul_sub, Units.val_mul, ← Units.val_mul γ⁻¹ γ, inv_mul_cancel, Units.val_one]
      intro i j
      rw [e]
      refine mul_cong M hi' (fun k l => ?_) i j
      obtain ⟨b, hb, hb'⟩ := hsub k l
      exact ⟨b, hb, by rw [Matrix.sub_apply] at hb' ⊢; exact hb'⟩
    obtain ⟨x, hxK, γ₀, hγ₀, hreal, hfin⟩ := hcong (fun v => Formalism.L2.S.S7.DensRat.ratReal I (γ'⁻¹ * γ) hδ v)
      ⟨γ'⁻¹ * γ, ⟨hδ, c1, c2⟩, fun v => rfl⟩
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h0 : γ₀ = γ'⁻¹ * γ := Units.ext (eq_of_real I v (hreal v).symm)
    have hx : x = fp I (γ'⁻¹ * γ) hδ := by
      apply Subtype.ext; apply Units.ext
      exact hfin.trans (by rw [h0]; rfl)
    rw [← fp_mul I hT'.1 hγ, ← hx]
    exact hxK

end GlobalTheory.IntUnitCpt
end
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_integral_unitary_finitePart : ∀ I : AutInst, ∃ K : Set I.Gf, IsCompact K ∧ ∀ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) → (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) → ∃ x ∈ I.GFset, x.2 ∈ K ∧ ∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
  atlas_forward_decl GlobalTheory.IntUnitCpt.intUnit_compact
end

section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.HtMinPf

lemma uj_entry {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat g i j‖ = ‖uMat g⁻¹ j i‖ := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hmi : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
            rw [hg, hJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [hmi]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  by_cases ha : ε j <;> by_cases hb : ε i <;> simp [ha, hb]

variable (I : AutInst)

lemma vec_sum (y : I.Ginf) {N : ℕ} (z : Fin N → ℤ) (e : Fin N → Fin I.n → I.E) :
    vec I y (∑ i, z i • e i) = ∑ i, ((z i : ℝ)) • vec I y (e i) := by
  funext v
  have h : (fun k => I.φ v (∑ i, z i • e i k)) = ∑ i, ((z i : ℝ)) • fun k => I.φ v (e i k) := by
    funext k
    simp [Finset.sum_apply, map_sum, Complex.real_smul]
  simp only [CuspGeo.vec, Finset.sum_apply, Pi.smul_apply]
  rw [h, Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp [Matrix.mulVec_smul]

lemma vec_one (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    vec I y u v = uMat (y v)⁻¹ *ᵥ vec I 1 u v := by
  have h1 : uMat ((1 : I.Ginf) v)⁻¹ = 1 := by simp [uMat]
  simp only [CuspGeo.vec]
  rw [h1, Matrix.one_mulVec]

lemma vec_trans (x₁ y : I.Ginf) (γ : GL (Fin I.n) I.E)
    (hx : ∀ v, uMat (x₁ v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (u : Fin I.n → I.E) : vec I (x₁ * y) ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) = vec I y u := by
  funext v
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have hinv : uMat (x₁ v)⁻¹ * uMat (x₁ v) = 1 := by
    show (((x₁ v)⁻¹ : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val * ((x₁ v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have hφ : (fun i => I.φ v (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  have hmul : uMat ((x₁ * y) v)⁻¹ = uMat (y v)⁻¹ * uMat (x₁ v)⁻¹ := by
    simp [uMat, Pi.mul_apply, _root_.mul_inv_rev]
  simp only [CuspGeo.vec]
  rw [hmul, hφ, ← Matrix.mulVec_mulVec]
  congr 1
  have : (I.P v)⁻¹ *ᵥ ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i)) =
      uMat (x₁ v) *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)) := by
    rw [hx v, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (I.P v), hP, Matrix.mul_one]
  rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

lemma span_of_zbasis {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (he₀ : IsZBasis I e₀)
    (w : InfinitePlace I.F → Fin I.n → ℂ) : ∃ c : Fin N → ℝ, w = ∑ l, c l • vec I 1 (e₀ l) := by
  obtain ⟨N', e', ρ, d, hd, he', -, hdet⟩ := GlobalTheory.T.cusp_integralBasis_covolume_constant I
  set G := gm I ρ 1 e' with hGdef
  have hG : G.det ≠ 0 := by
    intro h
    have := hdet 1
    rw [← hGdef, h] at this
    simp at this
    linarith
  set a := G⁻¹ *ᵥ ρ w with ha
  have hGa : G *ᵥ a = ρ w := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.one_mulVec]
  have hw : w = ∑ j, a j • vec I 1 (e' j) := by
    apply ρ.injective
    rw [← hGa, map_sum]
    funext i
    simp [hGdef, gm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hz : ∀ j, ∃ z : Fin N → ℤ, e' j = ∑ i, z i • e₀ i := fun j =>
    (he₀.2 (e' j)).mp ((he'.2 (e' j)).mpr ⟨Pi.single j 1, by simp [Pi.single_apply]⟩)
  choose z hz using hz
  refine ⟨fun i => ∑ j, a j * (z j i : ℝ), ?_⟩
  rw [hw]
  simp_rw [hz, vec_sum, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

open Classical in
lemma entry_bound (z : I.Ginf) {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (c : Fin N → ℝ)
    (v : InfinitePlace I.F) (i : Fin I.n)
    (hc : (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l))
    (j : Fin I.n) : ‖uMat (z v)⁻¹ j i‖ ≤ ∑ l, |c l| * ‖vec I z (e₀ l)‖ := by
  have h : uMat (z v)⁻¹ j i = (∑ l, c l • vec I z (e₀ l)) v j := by
    calc uMat (z v)⁻¹ j i
        = (uMat (z v)⁻¹ *ᵥ (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) v) j := by
          simp [Matrix.mulVec_single_one]
      _ = (uMat (z v)⁻¹ *ᵥ (∑ l, c l • vec I 1 (e₀ l)) v) j := by rw [hc]
      _ = (∑ l, c l • vec I z (e₀ l)) v j := by
          simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, vec_one I z]
  rw [h, Finset.sum_apply, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (vec I z (e₀ l) v) j).trans
    (norm_le_pi_norm (vec I z (e₀ l)) v)) (abs_nonneg _)

end GlobalTheory.HtMinPf

open GlobalTheory.HtMinPf in

theorem GlobalTheory.htMin_of_reduced : ∀ I : AutInst, HtMin I := by
  intro I
  classical
  obtain ⟨N, R, C, hred⟩ := GlobalTheory.T.existsReducedBasisBoundedType_of_instance I
  obtain ⟨S, hSfin, hS0, hS⟩ := GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses I N R
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.T.exists_compact_integral_unitary_finitePart I
  have hbd : ∀ e₀ : Fin N → Fin I.n → I.E, ∃ M : ℝ, e₀ ∈ S → ∀ v i, ∃ c : Fin N → ℝ,
      (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l) ∧
        ∑ l, |c l| ≤ M := by
    intro e₀
    by_cases h : e₀ ∈ S
    · have := fun v i => span_of_zbasis I e₀ (hS0 e₀ h) (Pi.single v (Pi.single i (1 : ℂ)))
      choose c hc using this
      refine ⟨∑ v, ∑ i, ∑ l, |c v i l|, fun _ v i => ⟨c v i, hc v i, ?_⟩⟩
      calc ∑ l, |c v i l| ≤ ∑ i', ∑ l, |c v i' l| :=
            Finset.single_le_sum (f := fun i' => ∑ l, |c v i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ v', ∑ i', ∑ l, |c v' i' l| :=
            Finset.single_le_sum (f := fun v' => ∑ i', ∑ l, |c v' i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ v)
    · exact ⟨0, fun h' => absurd h' h⟩
  choose M hM using hbd
  obtain ⟨Mt, hMt⟩ := (hSfin.image M).bddAbove
  refine ⟨N, Mt * max C 0, K, hK, ?_⟩
  intro y t ht0 ht1 hns
  obtain ⟨e, heZ, heB, hesz⟩ := hred y
  obtain ⟨e₀, he₀S, γ, hγU, hγi, hγi', hγe⟩ := hS e heZ heB
  obtain ⟨x, hxG, hxK, hx⟩ := hK' γ hγU hγi hγi'
  refine ⟨x, hxG, hxK, fun v i j => ?_⟩
  have hMle : M e₀ ≤ Mt := hMt (Set.mem_image_of_mem M he₀S)
  obtain ⟨c, hc, hcM⟩ := hM e₀ he₀S v i
  have hvec : ∀ l, vec I (x.1 * y) (e₀ l) = vec I y (e l) := fun l => by
    rw [← hγe l]
    exact vec_trans I x.1 y γ hx (e l)
  have hb := entry_bound I (x.1 * y) e₀ c v i hc j
  simp_rw [hvec] at hb
  have ht : 0 ≤ t ^ N := pow_nonneg ht0.le _
  rw [uj_entry]
  calc ‖uMat ((x.1 * y) v)⁻¹ j i‖ * t ^ N ≤ (∑ l, |c l| * ‖vec I y (e l)‖) * t ^ N :=
        mul_le_mul_of_nonneg_right hb ht
    _ = ∑ l, |c l| * (‖vec I y (e l)‖ * t ^ N) := by
        rw [Finset.sum_mul]
        simp_rw [mul_assoc]
    _ ≤ ∑ l, |c l| * max C 0 := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left ((hesz t ht0 ht1 hns l).trans (le_max_left _ _)) (abs_nonneg _)
    _ = (∑ l, |c l|) * max C 0 := by rw [Finset.sum_mul]
    _ ≤ Mt * max C 0 := mul_le_mul_of_nonneg_right (hcM.trans hMle) (le_max_right _ _)
end

section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup : ∀ I : AutInst, HtMin I := by
  first | exact @GlobalTheory.htMin_of_reduced | exact GlobalTheory.htMin_of_reduced | (intros; apply GlobalTheory.htMin_of_reduced <;> assumption)
end

section
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S Formalism.UG

namespace GlobalTheory.CuspGeo

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hg : cT s g * J * g = J) (x y : Fin n → A) : hform s J (g *ᵥ x) (g *ᵥ y) = hform s J x y := by
  have h1 : ∀ x y : Fin n → A, hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := fun x y => by
    simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, Function.comp_apply]
  have h2 : s ∘ (g *ᵥ x) = g.map s *ᵥ (s ∘ x) := funext fun i => RingHom.map_mulVec s g x i
  rw [h1, h1, h2]
  conv_rhs => rw [← hg, ← mulVec_mulVec, ← mulVec_mulVec, cT, mulVec_transpose]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]

theorem inUnipRad_conj (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA WA' : Submodule A (Fin I.n → A)) (g gi m : Matrix (Fin I.n) (Fin I.n) A) (hgi : gi * g = 1)
    (hU : ∀ x y, hform s JA (g *ᵥ x) (g *ᵥ y) = hform s JA x y) (h1 : ∀ x ∈ WA, g *ᵥ x ∈ WA')
    (h2 : ∀ y ∈ WA', ∃ x ∈ WA, y = g *ᵥ x) (hm : I.InUnipRad s JA WA' m) :
    I.InUnipRad s JA WA (gi * m * g) := by
  obtain ⟨m1, m2, m3⟩ := hm
  have e : gi * m * g - 1 = gi * (m - 1) * g := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgi]
  have e' : ∀ z, (gi * m * g - 1) *ᵥ z = gi *ᵥ ((m - 1) *ᵥ (g *ᵥ z)) := fun z => by
    rw [e, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have back : ∀ x, gi *ᵥ (g *ᵥ x) = x := fun x => by rw [mulVec_mulVec, hgi, one_mulVec]
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
  · rw [e', m1 _ (h1 x hx), mulVec_zero]
  · have hy' : g *ᵥ y ∈ {y | ∀ x ∈ WA', hform s JA x y = 0} := fun x' hx' => by
      obtain ⟨x, hx, rfl⟩ := h2 x' hx'
      rw [hU]; exact hy x hx
    obtain ⟨x, hx, hxe⟩ := h2 _ (m2 _ hy')
    rw [e', hxe, back]; exact hx
  · rw [e', ← hU, mulVec_mulVec _ g gi, mul_eq_one_comm.1 hgi, one_mulVec]
    exact m3 (g *ᵥ y) _ (h1 x hx)

theorem span_map_mulVec {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} (c : Matrix (Fin n) (Fin n) E)
    (W : Submodule E (Fin n → E)) :
    (∀ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)),
      c.map ι *ᵥ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))) ∧
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)),
      ∃ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)), y = c.map ι *ᵥ x := by
  have key : ∀ w : Fin n → E, (c.map ι *ᵥ fun i => ι (w i)) = fun i => ι ((c *ᵥ w) i) := fun w =>
    funext fun i => (RingHom.map_mulVec ι c w i).symm
  constructor
  · intro x hx
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))).comap
          (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, mulVecLin_apply, key]
      exact Submodule.subset_span ⟨c *ᵥ w, ⟨w, hw, rfl⟩, rfl⟩
    exact this hx
  · intro y hy
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _))).map (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨w, hw, rfl⟩, by rw [mulVecLin_apply, key]; rfl⟩
    obtain ⟨x, hx, rfl⟩ := this hy
    exact ⟨x, hx, rfl⟩

theorem naconj : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧
    ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  intro I γ hγ W hW
  obtain ⟨c, hcU, hinf, hfin⟩ := hγ
  have hcU' : cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (c : Matrix (Fin I.n) (Fin I.n) I.E) =
      I.J := hcU
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨W.map (c : Matrix (Fin I.n) (Fin I.n) I.E).mulVecLin, ⟨?_, ?_⟩, fun m hm => ?_⟩
  · intro h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
    have : (c : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = 0 := by
      rw [← Submodule.mem_bot I.E, ← h]
      exact ⟨w, hw, rfl⟩
    apply hw0
    rw [← one_mulVec w, ← c.inv_mul, ← mulVec_mulVec, this, mulVec_zero]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, hform_mulVec_mulVec _ _ _ hcU']
    exact hW.2 x hx y hy
  obtain ⟨hmi, hmf⟩ := hm
  refine ⟨fun v => ?_, ?_⟩
  · have hst : ∀ y : I.E, I.φ v (star y) = star (I.φ v y) := fun y => hcm.2.2.2 (I.φ v) y
    have hPd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    have hPP : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ hPd
    have hPP' : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPd
    have hg : I.P v * uMat (γ.1 v) * (I.P v)⁻¹ = (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) := by
      rw [hinf v, Matrix.mul_assoc, Matrix.mul_assoc, hPP', Matrix.mul_one, ← Matrix.mul_assoc, hPP',
        Matrix.one_mul]
    have hu : ∀ a : Formalism.REAL.UJ (I.ε v), uMat a⁻¹ * uMat a = 1 := fun a => by simp [uMat]
    have hmul : ∀ a b : Formalism.REAL.UJ (I.ε v), uMat (a * b) = uMat a * uMat b := fun a b => by simp [uMat]
    have hgi : (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) = 1 := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
      rw [← Matrix.mul_assoc (uMat _), hu, Matrix.one_mul, hPP']
    have hconj : I.P v * uMat ((γ⁻¹ * m * γ).1 v) * (I.P v)⁻¹ = (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) *
        (I.P v * uMat (m.1 v) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) := by
      show I.P v * uMat ((γ.1 v)⁻¹ * m.1 v * γ.1 v) * (I.P v)⁻¹ = _
      rw [hmul, hmul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
    have hU : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.J.map (I.φ v) *
        (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      have e : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
          (cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) := by
        ext a b
        simp only [cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
        exact (hst _).symm
      rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hcU']
    obtain ⟨s1, s2⟩ := span_map_mulVec (I.φ v) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ (hmi v)
    · rw [hg]; exact hform_mulVec_mulVec _ _ _ hU
    · rw [hg]; exact s1
    · rw [hg]; exact s2
  · have hfm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by simp [AutInst.fmat]
    have hgi : I.fmat γ.2⁻¹ * I.fmat γ.2 = 1 := by rw [← hfm, inv_mul_cancel]; simp [AutInst.fmat]
    have hconj : I.fmat (γ⁻¹ * m * γ).2 = I.fmat γ.2⁻¹ * I.fmat m.2 * I.fmat γ.2 := by
      show I.fmat (γ.2⁻¹ * m.2 * γ.2) = _
      rw [hfm, hfm]
    have hU : cT (sigR I.cm.sig (Af I.F)) (I.fmat γ.2) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat γ.2 =
        I.J.map (inclE (F := I.F) (Af I.F)) := γ.2.2
    obtain ⟨s1, s2⟩ := span_map_mulVec (inclE (F := I.F) (Af I.F)) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ hmf
    · exact hform_mulVec_mulVec _ _ _ hU
    · rw [hfin]; exact s1
    · rw [hfin]; exact s2

end GlobalTheory.CuspGeo
end
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_conj_unipotentRadical_isotropic : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧ ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  atlas_forward_decl GlobalTheory.CuspGeo.naconj
end

section
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo.FirstMinPos

theorem norm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A *ᵥ x‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(A *ᵥ x) i‖ = ‖∑ j, A i j * x j‖ := rfl
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

variable (I : AutInst)

theorem exists_one_le_norm {a : I.E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) : ∃ v, 1 ≤ ‖I.φ v a‖ := by
  have hs : ∀ v (b : I.E), I.φ v (star b) = star (I.φ v b) := fun v b => I.cm.cmUnram.2.1 _ b
  by_contra hc
  push_neg at hc
  have hfin := CompanionTheory.D.gk.RF.PE.finite_bdd I hs 1
  have hmem : ∀ k : ℕ, a ^ k ∈ {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ 1} := fun k =>
    ⟨ha.pow k, fun v => by rw [map_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc v).le⟩
  obtain ⟨m, k, hmk, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hpos : 0 < ‖I.φ v a‖ := norm_pos_iff.2 ((map_ne_zero _).2 h0)
  have h1 := congrArg (fun b => ‖I.φ v b‖) he
  simp only [map_pow, norm_pow] at h1
  exact absurd h1 (pow_lt_pow_right_of_lt_one₀ hpos (hc v) hmk).ne'

theorem coords_eq (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    (fun i => I.φ v (u i)) = (I.P v * uMat (y v)) *ᵥ vec I y u v := by
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hy : uMat (y v) * uMat (y v)⁻¹ = 1 := CompanionTheory.D.gk.RF.PE.uMat_mul_inv (y v)
  simp only [vec, mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uMat (y v)), hy, Matrix.one_mul, hP, one_mulVec]

def cst (y : I.Ginf) (v : InfinitePlace I.F) : ℝ := ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖

theorem cst_nonneg (y : I.Ginf) (v : InfinitePlace I.F) : 0 ≤ cst I y v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_phi_le (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) (i : Fin I.n) :
    ‖I.φ v (u i)‖ ≤ cst I y v * ‖vec I y u‖ := by
  have e := congrFun (coords_eq I y u v) i
  calc ‖I.φ v (u i)‖ = ‖((I.P v * uMat (y v)) *ᵥ vec I y u v) i‖ := by rw [← e]
    _ ≤ ‖(I.P v * uMat (y v)) *ᵥ vec I y u v‖ := norm_le_pi_norm _ i
    _ ≤ cst I y v * ‖vec I y u v‖ := norm_mulVec_le _ _
    _ ≤ cst I y v * ‖vec I y u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ v) (cst_nonneg I y v)

end GlobalTheory.CuspGeo.FirstMinPos

namespace GlobalTheory.CuspGeo

open FirstMinPos in

theorem firstMin_pos : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  intro I y
  have hK0 : 0 < ∑ v, cst I y v + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun v _ => cst_nonneg I y v) one_pos
  refine ⟨1 / (∑ v, cst I y v + 1), by positivity, fun u hu h0 => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (funext hc)
  obtain ⟨v, hv⟩ := exists_one_le_norm I (hu i) hi
  have h2 : cst I y v ≤ ∑ v, cst I y v + 1 := by
    have := Finset.single_le_sum (f := cst I y) (fun v _ => cst_nonneg I y v) (Finset.mem_univ v)
    linarith
  rw [div_le_iff₀ hK0]
  calc (1 : ℝ) ≤ cst I y v * ‖vec I y u‖ := hv.trans (norm_phi_le I y u v i)
    _ ≤ (∑ v, cst I y v + 1) * ‖vec I y u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖vec I y u‖ * (∑ v, cst I y v + 1) := mul_comm _ _

end GlobalTheory.CuspGeo

end
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  atlas_forward_decl GlobalTheory.CuspGeo.firstMin_pos
end

section
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo

section

variable (I : AutInst)

theorem hform_eq_dot {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : Formalism.UG.hform (starRingEnd K) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_NInf_of_NA {W : Submodule I.E (Fin I.n → I.E)} {m : I.Ginf} (hm : ((m, 1) : I.GA) ∈ I.NA W) :
    m ∈ CompanionTheory.D.gk.RF.NInf I W := by
  intro v
  obtain ⟨h1, h2, h3⟩ := hm.1 v
  show CompanionTheory.D.gk.RF.Lowers (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) (uMat (m v) - 1)
  have hdet := CompanionTheory.D.gk.RF.P_det I v
  have hPi : I.P v * (I.P v)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hiP : (I.P v)⁻¹ * I.P v = 1 := nonsing_inv_mul _ hdet
  have hB : ∀ z, (I.P v * uMat (m v) * (I.P v)⁻¹ - 1) *ᵥ (I.P v *ᵥ z) =
      I.P v *ᵥ ((uMat (m v) - 1) *ᵥ z) := fun z => by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ (I.P v)⁻¹ (I.P v), hiP,
      Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  have hWC : ∀ w ∈ CompanionTheory.D.gk.RF.Wv I W v, I.P v *ᵥ w ∈
      Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [CompanionTheory.D.gk.RF.P_atV]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hWv : ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      (I.P v)⁻¹ *ᵥ x ∈ CompanionTheory.D.gk.RF.Wv I W v := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hfP : ∀ w z, CompanionTheory.D.gk.RF.hf (Formalism.REAL.Jm (I.ε v)) w z =
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) (I.P v *ᵥ w) (I.P v *ᵥ z) := fun w z => by
    rw [hform_eq_dot, CompanionTheory.D.gk.RF.hf, ← I.P_spec v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      mulVec_mulVec, Matrix.mul_assoc]
  have hc1 : ∀ z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v),
      ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0 := fun z hz x hx => by
    have e : x = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ x) := by rw [mulVec_mulVec, hPi, one_mulVec]
    rw [e, ← hfP]
    exact hz _ (hWv x hx)
  have hc2 : ∀ z, (∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0) →
      z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) := fun z h w hw => by
    rw [hfP]
    exact h _ (hWC w hw)
  have inj : ∀ a : Fin I.n → ℂ, a = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ a) := fun a => by
    rw [mulVec_mulVec, hiP, one_mulVec]
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · have := h1 _ (hWC w hw)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ w), this, mulVec_zero]
  · have := h2 _ (hc1 z hz)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ z)]
    exact hWv _ this
  · refine hc2 _ fun x hx => ?_
    have := h3 (I.P v *ᵥ z)
    rw [hB] at this
    exact this x hx

theorem shortCusp_holds : ShortCusp I := by
  intro U hU
  obtain ⟨M, hM, hMU⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I U hU
  obtain ⟨s₁, hs₁, hSI⟩ := CompanionTheory.D.gk.RF.short_isotropic_vector_of CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₁, hC₁, hCS⟩ := CompanionTheory.D.gk.RF.covolume_span I
  obtain ⟨C₂, hC₂, hCP⟩ := CompanionTheory.D.gk.RF.covolume_orthogonal_complement CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₃, hC₃, hNC⟩ := CompanionTheory.D.gk.RF.nilpotent_cover_of CompanionTheory.D.gk.RF.transport_to_standard_form CompanionTheory.D.gk.RF.gamSub
    CompanionTheory.D.gk.RF.nilpotent_lie_algebra CompanionTheory.D.gk.RF.nilpotent_subgroup_representation I M hM
  set s₀ := min s₁ 1
  have hs₀ : 0 < s₀ := lt_min hs₁ one_pos
  have hD : 0 < 2 * (C₁ + C₂ + 1) := by positivity
  refine ⟨s₀, 1 / (2 * (C₁ + C₂ + 1)), C₃ * (C₁ + C₂), hs₀, by positivity, fun y η hη hηη₀ hc => ?_⟩
  have hηD : η * (2 * (C₁ + C₂ + 1)) ≤ 1 := (le_div_iff₀ hD).1 hηη₀
  have hη1 : η < 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηb : (C₁ + C₂) * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηa : 2 * C₁ * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  obtain ⟨u, hu, hu0, hus⟩ := hc
  have hc' : ∃ u ∈ CompanionTheory.D.gk.RF.IntV I, u ≠ 0 ∧ ‖CompanionTheory.D.gk.RF.vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    ⟨u, hu, hu0, hus⟩
  obtain ⟨t, ht, hts, d, w, hd, hw, hne, hall⟩ := CompanionTheory.D.gk.RF.successive_minima_gap I.E I.n (CompanionTheory.D.gk.RF.IntV I)
    (fun u => ‖CompanionTheory.D.gk.RF.vecAt I y u‖) s₀ η hs₀ hη hη1 hc'
  have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
  have hs : η * t ≤ s₁ := (mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))
  have hI : CompanionTheory.D.gk.RF.Isot I.J (Submodule.span I.E (Set.range w)) := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact CompanionTheory.D.gk.RF.mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))
  have c1 := hCS y d w (η * t) hd (by positivity) hw
  have c2 := hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by
    by_contra h
    exact hn (hall u hu (not_le.1 h).le)
  have hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η := by
    have e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η := by field_simp
    have : η * t * t ≤ 1 := mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1
    have := mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this
    rw [e]; linarith
  refine ⟨Submodule.span I.E (Set.range w), ⟨hne, fun x hx z hz => ?_⟩, fun m hm => ?_⟩
  · have := hI hz x hx
    rw [hform_eq_dot]
    exact this
  obtain ⟨γ, h1, -, h3⟩ := hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity)
    (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity)))
    (c2.mono (le_add_of_nonneg_left (by positivity))) m (mem_NInf_of_NA I hm)
  obtain ⟨x, hxU, hx⟩ := hMU γ h1
  refine ⟨(γ, x), hx, hxU, fun v i j => (h3 v i j).trans ?_⟩
  rw [mul_assoc C₃]
  exact mul_le_mul_of_nonneg_left hρ hC₃.le

end

theorem shortCusp_all : ∀ I : AutInst, ShortCusp I := shortCusp_holds

end GlobalTheory.CuspGeo
end
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances : ∀ I : AutInst, ShortCusp I := by
  atlas_forward_decl GlobalTheory.CuspGeo.shortCusp_all
end

section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo

theorem exists_scale_of_bdd {ι : Type*} (N : ι → ℝ) (t a : ℝ) (ht : 0 < t) (hN : ∀ i, t ≤ N i) (ha : 0 < a) :
    ∃ m : ℝ, 0 < m ∧ m ≤ a ∧ (∀ i, m / 2 ≤ N i) ∧ (m = a ∨ ∃ i, N i ≤ m) := by
  by_cases h : ∃ i, N i ≤ a
  · obtain ⟨i₀, hi₀⟩ := h
    have hbdd : BddBelow (Set.range N) := ⟨t, by rintro _ ⟨i, rfl⟩; exact hN i⟩
    haveI : Nonempty ι := ⟨i₀⟩
    have hl : t ≤ ⨅ i, N i := le_ciInf hN
    have hle : ∀ i, ⨅ i, N i ≤ N i := fun i => ciInf_le hbdd i
    refine ⟨min (2 * ⨅ i, N i) a, lt_min (by linarith) ha, min_le_right _ _, fun i => ?_, ?_⟩
    · have h1 := hle i
      have h2 := min_le_left (2 * ⨅ i, N i) a
      linarith
    · rcases le_total (2 * ⨅ i, N i) a with h2 | h2
      · right
        rw [min_eq_left h2]
        obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt (show ⨅ i, N i < 2 * ⨅ i, N i by linarith)
        exact ⟨i, hi.le⟩
      · left
        exact min_eq_right h2
  · push_neg at h
    exact ⟨a, ha, le_rfl, fun i => by linarith [h i], Or.inl rfl⟩

theorem exists_root_scale (n : ℕ) (s₀ m : ℝ) (hs : 0 < s₀) (hm : 0 < m) :
    ∃ η : ℝ, 0 < η ∧ s₀ * η ^ (n + 1) = m := by
  refine ⟨(m / s₀) ^ ((((n + 1 : ℕ) : ℝ))⁻¹), Real.rpow_pos_of_pos (div_pos hm hs) _, ?_⟩
  rw [Real.rpow_inv_natCast_pow (div_pos hm hs).le (Nat.succ_ne_zero n)]
  field_simp

theorem exists_scale_real (I : AutInst) (y : I.Ginf) (s₀ η₀ : ℝ) (hs : 0 < s₀) (hη : 0 < η₀) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η₀ ∧ NoShort I y (s₀ / 2 * η ^ (I.n + 1)) ∧
      (η₀ ≤ η ∨ ∃ u, IntVec I u ∧ u ≠ 0 ∧ ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1)) := by
  obtain ⟨t, ht, hNS⟩ := GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint I y
  obtain ⟨m, hm0, hma, hmN, hmc⟩ := exists_scale_of_bdd (ι := {u // IntVec I u ∧ u ≠ 0})
    (fun u => ‖vec I y u.1‖) t (s₀ * η₀ ^ (I.n + 1)) ht (fun u => hNS u.1 u.2.1 u.2.2) (by positivity)
  obtain ⟨η, hη0, hηm⟩ := exists_root_scale I.n s₀ m hs hm0
  have hpow : η ^ (I.n + 1) ≤ η₀ ^ (I.n + 1) := le_of_mul_le_mul_left (by rw [hηm]; exact hma) hs
  refine ⟨η, hη0, (pow_le_pow_iff_left₀ hη0.le hη.le (Nat.succ_ne_zero _)).1 hpow, fun u hu hu0 => ?_, ?_⟩
  · have h1 := hmN ⟨u, hu, hu0⟩
    have h2 : s₀ / 2 * η ^ (I.n + 1) = m / 2 := by rw [← hηm]; ring
    rw [h2]
    exact h1
  · rcases hmc with h | ⟨⟨u, hu, hu0⟩, hle⟩
    · left
      have : η₀ ^ (I.n + 1) ≤ η ^ (I.n + 1) := le_of_mul_le_mul_left (by rw [hηm, h]) hs
      exact (pow_le_pow_iff_left₀ hη.le hη0.le (Nat.succ_ne_zero _)).1 this
    · right
      exact ⟨u, hu, hu0, hηm ▸ hle⟩

theorem close_mono (I : AutInst) {u : I.Ginf} {a b : ℝ} (h : Close I u a) (hab : a ≤ b) : Close I u b :=
  fun v i j => (h v i j).trans hab

end GlobalTheory.CuspGeo

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.MainNotions.LeviCoordinates in

theorem nearInst : ∀ I : AutInst, NearInst I := by
  intro I Kp hKo
  have hmem : ∀ {g : I.GA}, g ∈ I.GFset ↔ g ∈ rr_GF I := fun {g} => by
    rw [← SetLike.mem_coe, rr_GF_coe]
  obtain ⟨-, -, -, hKsC, hKsO, ⟨Ks, hKs⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  set Kq : Subgroup I.Gf := Kp ⊓ Ks with hKq
  have hKqO : IsOpen (Kq : Set I.Gf) := by
    rw [hKq, Subgroup.coe_inf, hKs]; exact hKo.inter hKsO
  have hKqC : IsCompact (Kq : Set I.Gf) :=
    hKsC.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKqO)
      (by rw [← hKs]; exact fun z hz => (Subgroup.mem_inf.1 hz).2)
  obtain ⟨S, hS⟩ := adelic_class_set_finite I Kq hKqO
  set U : Set I.Gf := {g | ∀ s ∈ S, s⁻¹ * g * s ∈ Kq} with hUdef
  have hU : U ∈ 𝓝 (1 : I.Gf) := by
    have : ∀ s ∈ S, ∀ᶠ g in 𝓝 (1 : I.Gf), s⁻¹ * g * s ∈ Kq := fun s _ =>
      (hKqO.preimage (by fun_prop : Continuous fun g : I.Gf => s⁻¹ * g * s)).mem_nhds (by simp)
    exact (Filter.eventually_all_finset S).2 this
  obtain ⟨s₀, η₀, Cs, hs₀, hη₀, hSC⟩ := GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances I U hU
  obtain ⟨b, CH, KH, hKH, hHt⟩ := GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup I
  set s₁ := min s₀ 1 with hs₁
  set η₁ := min η₀ 1 with hη₁
  have hs₁0 : 0 < s₁ := lt_min hs₀ one_pos
  have hη₁0 : 0 < η₁ := lt_min hη₀ one_pos
  set C := max (CH / (s₁ / 2) ^ b) Cs with hC
  refine ⟨(I.n + 1) * b, C, η₁, (fun p : I.Gf × I.Gf × I.Gf => p.1 * p.2.1 * p.2.2) '' (KH ×ˢ ((S : Set I.Gf) ×ˢ (Kq : Set I.Gf))),
    hη₁0, (hKH.prod (S.finite_toSet.isCompact.prod hKqC)).image (by fun_prop), fun x => ?_⟩
  obtain ⟨γf, ⟨γE, hγE, hγEf⟩, s, hsS, k, hk, hx2⟩ := hS x.2
  set γ₀ : I.GA := (fun v => Formalism.L2.S.S7.DensRat.ratReal I γE hγE v, γf) with hγ₀def
  have hγ₀ : γ₀ ∈ I.GFset := ⟨γE, hγE, fun _ => rfl, hγEf⟩
  set y : I.Ginf := γ₀.1⁻¹ * x.1 with hy
  have hx : x = γ₀ * ((y, s * k) : I.GA) :=
    Prod.ext (by simp [hy]) (by simp [hγ₀def, hx2, mul_assoc])
  obtain ⟨η, hη0, hηle, hNS, hcase⟩ := exists_scale_real I y s₁ η₁ hs₁0 hη₁0
  have hη1 : η ≤ 1 := hηle.trans (min_le_right _ _)
  set t := s₁ / 2 * η ^ (I.n + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    have h1 : s₁ ≤ 1 := min_le_right _ _
    have h2 : η ^ (I.n + 1) ≤ 1 := pow_le_one₀ hη0.le hη1
    have h3 : 0 ≤ η ^ (I.n + 1) := by positivity
    nlinarith
  obtain ⟨γ₁, hγ₁, hγ₁K, hγ₁b⟩ := hHt y t ht0 ht1 hNS
  refine ⟨η, hη0, hη1, ⟨γ₁ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem (hmem.1 hγ₁) ((rr_GF I).inv_mem (hmem.1 hγ₀))), ?_, ?_⟩, ?_⟩
  · refine ⟨(γ₁.2, s, k), ⟨hγ₁K, hsS, hk⟩, ?_⟩
    rw [hx]
    simp [mul_assoc]
  · intro v i j
    have e1 : (γ₁ * γ₀⁻¹ * x).1 = γ₁.1 * y := by rw [hx]; simp [mul_assoc]
    rw [e1]
    have hb := hγ₁b v i j
    have hpos : 0 < (s₁ / 2) ^ b := by positivity
    have e2 : t ^ b = (s₁ / 2) ^ b * η ^ ((I.n + 1) * b) := by rw [ht, mul_pow, pow_mul]
    rw [e2] at hb
    have h3 : ‖uMat ((γ₁.1 * y) v) i j‖ * η ^ ((I.n + 1) * b) ≤ CH / (s₁ / 2) ^ b := by
      rw [le_div_iff₀ hpos]; linarith
    exact h3.trans (le_max_left _ _)
  rcases hcase with h | ⟨u, hu, hu0, hul⟩
  · exact Or.inl h
  right
  have hul' : ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    hul.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  obtain ⟨W, hW, hcov⟩ := hSC y η hη0 (hηle.trans (min_le_left _ _)) ⟨u, hu, hu0, hul'⟩
  obtain ⟨W', hW', hconj⟩ := GlobalTheory.T.rational_conj_unipotentRadical_isotropic I γ₀ hγ₀ W hW
  obtain ⟨⟨N, hN⟩, -, hpart, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I W hW
  refine ⟨W', hW', fun m hm => ?_⟩
  have hm' : γ₀⁻¹ * m * γ₀ ∈ I.NA W := hconj m hm
  obtain ⟨γ₂, ⟨hγ₂, hγ₂N⟩, hγ₂U⟩ := hdense U hU _ hm'
  set m'' := γ₂⁻¹ * (γ₀⁻¹ * m * γ₀) with hm''
  have hm''N : m'' ∈ I.NA W := by
    rw [← hN] at hm' hγ₂N ⊢
    exact N.mul_mem (N.inv_mem hγ₂N) hm'
  obtain ⟨γ₃, hγ₃, hγ₃U, hclose⟩ := hcov m''.1 (hpart m'' hm''N).1
  refine ⟨γ₀ * γ₂ * γ₃⁻¹ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem ((rr_GF I).mul_mem ((rr_GF I).mul_mem (hmem.1 hγ₀)
    (hmem.1 hγ₂)) ((rr_GF I).inv_mem (hmem.1 hγ₃))) ((rr_GF I).inv_mem (hmem.1 hγ₀))),
    y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k), ?_, ?_,
    close_mono I hclose (mul_le_mul_of_nonneg_right (le_max_right _ _) hη0.le)⟩
  · have e : (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k) = k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k := by group
    rw [e]
    have hk' : k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k ∈ Kq :=
      Kq.mul_mem (Kq.mul_mem (Kq.inv_mem hk) (Kq.mul_mem (hγ₃U s hsS) (hγ₂U s hsS))) hk
    exact (Subgroup.mem_inf.1 hk').1
  · have hyu : ((y, s * k) : I.GA) * (y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k)) =
        γ₃ * m'' * (y, s * k) := Prod.ext (by simp; group) (by simp; group)
    have hmm : m = γ₀ * γ₂ * m'' * γ₀⁻¹ := by rw [hm'']; group
    calc m * x = γ₀ * γ₂ * γ₃⁻¹ * (γ₃ * m'' * (y, s * k)) := by rw [hmm, hx]; group
      _ = _ := by rw [← hyu, hx]; group

end GlobalTheory.CuspGeo
end
end
end

section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoint_nearCusp_scale : ∀ I : AutInst, NearInst I := by
  first | exact @GlobalTheory.CuspGeo.nearInst | exact GlobalTheory.CuspGeo.nearInst | (intros; apply GlobalTheory.CuspGeo.nearInst <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.IndefR.Eqv

theorem norm_mul_mul_apply_le {n : ℕ} (P A Q : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hA : ∀ k l, ‖A k l‖ ≤ c)
    (i j : Fin n) : ‖(P * A * Q) i j‖ ≤ (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
  simp only [Matrix.mul_apply]
  calc ‖∑ l, (∑ k, P i k * A k l) * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * c * ‖Q l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, ← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hA k l) (norm_nonneg _)
    _ = (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem norm_uMat_inv_apply {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat y⁻¹ i j‖ = ‖uMat y j i‖ := by
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y = Formalism.REAL.Jm ε := y.2
  have h1 : uMat y⁻¹ = Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε := by
    show (((y : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
    refine Units.inv_eq_of_mul_eq_one_left ?_
    calc Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y
        = Formalism.REAL.Jm ε * ((uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]
  rw [h1]
  by_cases hi : ε i <;> by_cases hj : ε j <;>
    simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hi, hj]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def frameBound (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : ℝ :=
  ∑ k, ∑ l, ‖fr.P (Formalism.L2.Host.tauPl D τ) i k‖ * ‖(fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ l j‖

theorem frameBound_nonneg (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : 0 ≤ frameBound fr τ i j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

def brgFin (fr : UI.Frames D V) : (UI.instV fr).Gf →* GA D V :=
  (UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inr _ _)

theorem brgFin_apply (fr : UI.Frames D V) (k : (UI.instV fr).Gf) : brgFin fr k = UI.brg fr (1, k) := rfl

theorem continuous_brgFin (fr : UI.Frames D V) : Continuous (brgFin fr) :=
  (UI.brg fr).continuous.comp (continuous_const.prodMk continuous_id)

theorem brg_entry_bounds (fr : UI.Frames D V)
    (h2 : ∀ (x : (UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr x) =
        fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (y : (UI.instV fr).Ginf) (c : ℝ),
      ((∀ v i j, ‖uMat (y v) i j‖ ≤ c) → normInf θ V (UI.brg fr (y, 1)) ≤ S * c) ∧
      ((∀ v i j, ‖(uMat (y v) - 1) i j‖ ≤ c) →
        ∀ τ i j, ‖(infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr (y, 1)) - 1) i j‖ ≤ S * c) := by
  have hle : ∀ τ i j, frameBound fr τ i j ≤ ∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j := fun τ i j => by
    have h0 := frameBound_nonneg fr
    calc frameBound fr τ i j ≤ 2 * frameBound fr τ i j := by linarith [h0 τ i j]
      _ ≤ ∑ j', 2 * frameBound fr τ i j' :=
          Finset.single_le_sum (f := fun j' => 2 * frameBound fr τ i j') (fun j' _ => by linarith [h0 τ i j'])
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', 2 * frameBound fr τ i' j' :=
          Finset.single_le_sum (f := fun i' => ∑ j', 2 * frameBound fr τ i' j')
            (fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ i' j']) (Finset.mem_univ i)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', 2 * frameBound fr τ' i' j')
            (fun τ' _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ' i' j'])
            (Finset.mem_univ τ)
  refine ⟨∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j,
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg zero_le_two (frameBound_nonneg fr τ i j), fun y c => ⟨fun hc => ?_, fun hc τ i j => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have e1 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c (fun k l => hc (Formalism.L2.Host.tauPl D τ) k l) i j
    have e2 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c
      (fun k l => (norm_uMat_inv_apply _ k l).trans_le (hc _ l k)) i j
    rw [← map_inv, h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl,
      h2 _ τ (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    unfold frameBound
    linarith
  · have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc (Formalism.L2.Host.tauPl D τ) i j)
    have hdet : IsUnit (fr.P (Formalism.L2.Host.tauPl D τ)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ))
    rw [h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    have e : fr.P (Formalism.L2.Host.tauPl D τ) * (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ - 1 = fr.P (Formalism.L2.Host.tauPl D τ) *
        ((uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) - 1) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hdet]
    rw [e]
    exact (norm_mul_mul_apply_le _ _ _ c (hc _) i j).trans (mul_le_mul_of_nonneg_right (hle τ i j) hc0)

theorem near (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    Near θ V := by
  intro U hU
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary D θ hθ V (UI.framesV D V)
  obtain ⟨S, hS0, hS⟩ := brg_entry_bounds (θ := θ) (UI.framesV D V) h2
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
  have hKp : IsOpen ((U.comap (brgFin (UI.framesV D V)) : Subgroup _) : Set (UI.instV (UI.framesV D V)).Gf) :=
    hU.preimage (continuous_brgFin _)
  obtain ⟨b, C, δ₀, K, hδ₀, hK, hx⟩ := GlobalTheory.T.adelicPoint_nearCusp_scale (UI.instV (UI.framesV D V)) _ hKp
  obtain ⟨Ck, hCk⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V (hK.image (continuous_brgFin (UI.framesV D V)))
  refine ⟨b * d, max (Ck * (S * C) ^ d) (S * C), δ₀, hδ₀, fun g => ?_⟩
  set fr := UI.framesV D V with hfr
  set x := (UI.brg fr).symm g with hxdef
  have hgx : UI.brg fr x = g := (UI.brg fr).apply_symm_apply g
  obtain ⟨δ, hδ, hδ1, ⟨γ, hγ, hγK, hγb⟩, halt⟩ := hx x
  refine ⟨δ, hδ, hδ1, ?_, ?_⟩
  · have hsplit : γ * x = ((γ * x).1, 1) * (1, (γ * x).2) := Prod.ext (by simp) (by simp)
    have e : UI.brg fr γ * g = UI.brg fr ((γ * x).1, 1) * brgFin fr (γ * x).2 := by
      calc UI.brg fr γ * g = UI.brg fr (γ * x) := by rw [map_mul, hgx]
        _ = UI.brg fr (((γ * x).1, 1) * (1, (γ * x).2)) := congrArg _ hsplit
        _ = _ := map_mul _ _ _
    have hkb := hCk _ ⟨_, hγK, rfl⟩
    have hq : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck := by
      have := GlobalTheory.Grow.quotHeight_le V g ((h1 γ).2 hγ)
      rw [e] at this
      exact this.trans ((GlobalTheory.Grow.height_mul_le V _ _).trans
        (mul_le_mul_of_nonneg_left hkb (GlobalTheory.Grow.height_pos V _).le))
    have hy : ∀ v i j, ‖uMat ((γ * x).1 v) i j‖ ≤ C / δ ^ b := fun v i j =>
      (le_div_iff₀ (pow_pos hδ b)).2 (hγb v i j)
    have hN := (hS (γ * x).1 (C / δ ^ b)).1 hy
    have hN0 : 0 ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) := by unfold normInf; positivity
    have hNb : normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b ≤ S * C := by
      calc _ ≤ S * (C / δ ^ b) * δ ^ b := mul_le_mul_of_nonneg_right hN (pow_pos hδ b).le
        _ = S * C := by rw [mul_assoc, div_mul_cancel₀ _ (pow_pos hδ b).ne']
    have hH := hd _ ((brg_mem_GinfC fr ((γ * x).1, 1)).2 rfl)
    have hHb : GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d) ≤ (S * C) ^ d := by
      rw [pow_mul]
      calc _ ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) ^ d * (δ ^ b) ^ d :=
            mul_le_mul_of_nonneg_right hH (by positivity)
        _ = (normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b) ^ d := (mul_pow _ _ _).symm
        _ ≤ (S * C) ^ d := pow_le_pow_left₀ (by positivity) hNb d
    have hCk0 : 0 ≤ Ck := zero_le_one.trans ((GlobalTheory.Grow.one_le_height V _).trans hkb)
    calc GlobalTheory.Grow.quotHeight V g * δ ^ (b * d)
        ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck * δ ^ (b * d) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = Ck * (GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d)) := by ring
      _ ≤ Ck * (S * C) ^ d := mul_le_mul_of_nonneg_left hHb hCk0
      _ ≤ _ := le_max_left _ _
  · rcases halt with h | ⟨W, hW, hWm⟩
    · exact Or.inl h
    · obtain ⟨r, C₀, hC₀, hNI⟩ := h3 W hW
      refine Or.inr ⟨r, C₀, hC₀, fun m hm => ?_⟩
      have hm' : (UI.brg fr).symm m ∈ (UI.instV fr).NA W :=
        hNI _ (by rwa [(UI.brg fr).apply_symm_apply])
      obtain ⟨γ', hγ', u, k, hk, he, hu⟩ := hWm _ hm'
      refine ⟨UI.brg fr γ', (h1 γ').2 hγ', UI.brg fr (u, 1), brgFin fr k,
        ⟨(brg_mem_GinfC fr (u, 1)).2 rfl, fun τ i j => ?_⟩, hk, (brg_mem_GfC fr (1, k)).2 rfl, ?_⟩
      · calc _ ≤ S * (C * δ) := (hS u (C * δ)).2 hu τ i j
          _ ≤ max (Ck * (S * C) ^ d) (S * C) * δ := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      · calc m * g = UI.brg fr ((UI.brg fr).symm m * x) := by rw [map_mul, (UI.brg fr).apply_symm_apply, hgx]
          _ = UI.brg fr (γ' * x * ((u, 1) * (1, k))) := by
            rw [he]; exact congrArg (fun z => UI.brg fr (γ' * x * z)) (Prod.ext (by simp) (by simp))
          _ = UI.brg fr γ' * g * UI.brg fr (u, 1) * brgFin fr k := by
            rw [map_mul, map_mul, map_mul, hgx, ← mul_assoc]; rfl

end GlobalTheory.CuspGeo
end
end
