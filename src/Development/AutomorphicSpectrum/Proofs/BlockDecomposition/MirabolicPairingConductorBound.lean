import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity

section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_coefficient_continuous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.continuous_coef | exact GlobalTheory.CompanionTheory.MirPair.continuous_coef | (intros; apply GlobalTheory.CompanionTheory.MirPair.continuous_coef <;> assumption)
end

section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem det_one_add_eLast {k : Type} [Field k] {n : ℕ} (b : Fin (n + 1) → k) :
    (1 + vecMulVec (eLast k n) b).det = 1 + b (Fin.last n) := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    GlobalTheory.BZMir.eLast, dotProduct_single, mul_one]

theorem shearGL_mulVec_and_nabs_det : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (b : Fin (n + 1) → k), valuation k (b (Fin.last n)) < 1 → (∀ x : Fin (n + 1) → k, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x = x + (b ⬝ᵥ x) • eLast k n) ∧ nabs k (Matrix.GeneralLinearGroup.det (shearGL n b)) = 1 := by
  intro k _ _ _ _ n b hb
  have hv : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hb
  have hdet := GlobalTheory.CompanionTheory.MirPair.det_one_add_eLast b
  have hunit : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    simp only [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hunit, IsUnit.unit_spec]
  refine ⟨fun x => ?_, ?_⟩
  · rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [Matrix.GeneralLinearGroup.val_det_apply, hcoe, hdet, hv]

end GlobalTheory.CompanionTheory.MirPair
end

section
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem twist_integral_eq_JJ_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB b M v v' hb hfix hM
  obtain ⟨hg, hdet⟩ := GlobalTheory.CompanionTheory.MirPair.shearGL_mulVec_and_nabs_det b hb
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hcoef : ∀ x, GlobalTheory.CompanionTheory.MirPair.coef T B v
      (T' (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) v') x =
      GlobalTheory.CompanionTheory.MirPair.coef T B v v'
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := hlevi (GlobalTheory.CompanionTheory.MirPair.shearGL n b) x v v'
    rw [hfix] at h
    rw [h, GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.val_absPow, hdet]
    simp
  have hgg : ∀ x : Fin (n + 1) → k,
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hset : {y : Fin (n + 1) → k | ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} = M := Set.ext fun y => hM y
  have key := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) *
      GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  rw [hdet, hset] at key
  simp only [hgg, Complex.ofReal_one, NNReal.coe_one, one_mul] at key
  rw [GlobalTheory.CompanionTheory.MirPair.JJ]
  simp_rw [hcoef]
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hlast : (x + (b ⬝ᵥ x) • GlobalTheory.BZMir.eLast k n) (Fin.last n) = x (Fin.last n) + b ⬝ᵥ x := by
    simp [GlobalTheory.BZMir.eLast]
  simp only [GlobalTheory.CompanionTheory.MirPair.wt]
  rw [hg x, hlast, show -(x (Fin.last n) + b ⬝ᵥ x) = -(b ⬝ᵥ x) + -x (Fin.last n) by ring,
    AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.CompanionTheory.MirPair

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_depth_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear
end

section
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_leviMir (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

theorem tendsto_shearGL_zero (n : ℕ) :
    Filter.Tendsto (shearGL (k := k) n) (𝓝 0) (𝓝 1) := by
  have key : ∀ b : Fin (n + 1) → k, 1 + b (Fin.last n) ≠ 0 →
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b ∧
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    intro b hb
    have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
      simp [GlobalTheory.BZMir.eLast, dotProduct_single]
    have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
        b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [vecMulVec_mul_vecMulVec, hd]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
      rw [← mul_one_add]
      exact inv_mul_cancel₀ hb
    have hmul : (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) *
        (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) = 1 := by
      rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
        one_smul, add_sub_cancel_right]
    have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
      ⟨⟨_, _, hmul, mul_eq_one_comm.mp hmul⟩, rfl⟩
    have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hu]
      exact hu.unit_spec
    refine ⟨hcoe, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hcoe]
    exact hmul
  have h0 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) := by
    have h := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using h
  have hev : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, 1 + b (Fin.last n) ≠ 0 := by
    have h1 : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, valuation k (b (Fin.last n)) < 1 :=
      (continuous_apply (Fin.last n)).continuousAt.preimage_mem_nhds
        (show {x : k | valuation k x < 1} ∈ 𝓝 ((fun b : Fin (n + 1) → k => b (Fin.last n)) 0) from h0)
    filter_upwards [h1] with b hb h
    have h2 := (valuation k).map_one_add_of_lt hb
    rw [h, map_zero] at h2
    exact zero_ne_one h2
  have hv : Continuous fun b : Fin (n + 1) → k => vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul (continuous_apply j)
  have hv0 : vecMulVec (GlobalTheory.BZMir.eLast k n) (0 : Fin (n + 1) → k) = 0 := by
    ext i j
    simp [vecMulVec_apply]
  have h1 : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b)
      (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun b : Fin (n + 1) → k =>
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
      continuous_const.add hv
    simpa [hv0] using hc.tendsto (0 : Fin (n + 1) → k)
  have hinv0 : Filter.Tendsto (fun b : Fin (n + 1) → k => (1 + b (Fin.last n))⁻¹) (𝓝 0) (𝓝 1) := by
    have h : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + b (Fin.last n)) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun b : Fin (n + 1) → k => (1 : k) + b (Fin.last n) :=
        continuous_const.add (continuous_apply (Fin.last n))
      simpa using hc.tendsto (0 : Fin (n + 1) → k)
    simpa using h.inv₀ one_ne_zero
  have h2 : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) (𝓝 0) (𝓝 1) := by
    have hconst : Filter.Tendsto (fun _ : Fin (n + 1) → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
        (𝓝 0) (𝓝 1) := tendsto_const_nhds
    have h := hconst.sub (hinv0.smul (hv.tendsto 0))
    simpa [hv0] using h
  have h1' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h1.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).1.symm
  have h2' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h2.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).2.symm
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply, inv_one, Units.val_one]
  exact h1'.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2')

theorem shear_fix_vector {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) :
    ∃ r : kˣ, valuation k (r : k) < 1 ∧
      ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  have hopen : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have htend : Filter.Tendsto (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b))
      (𝓝 0) (𝓝 1) := by
    have h := ((GlobalTheory.CompanionTheory.MirPair.continuous_leviMir (k := k) (n + 1)).tendsto 1).comp (GlobalTheory.CompanionTheory.MirPair.tendsto_shearGL_zero (k := k) n)
    rw [map_one] at h
    exact h
  have hΩ : (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) ⁻¹'
      {g | T g v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) :=
    htend (hopen.mem_nhds (by simp))
  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.exists_box_subset hΩ
  haveI : (valuation k).IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (valuation k)).1 inferInstance
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  by_cases hr1 : valuation k (r : k) < 1
  · exact ⟨r, hr1, fun b hb => hr hb⟩
  · refine ⟨Units.mk0 x hx0, by simpa using hx1, fun b hb => hr ?_⟩
    intro j
    have h1 : valuation k (b j) ≤ valuation k x := hb j
    show valuation k (b j) ≤ valuation k (r : k)
    exact le_trans h1 (le_trans hx1.le (not_lt.mp hr1))

end GlobalTheory.CompanionTheory.MirPair

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_small_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ v : V, ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MirPair.shear_fix_vector
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearLat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dotProduct_eLast {n : ℕ} (b : Fin (n + 1) → k) : b ⬝ᵥ eLast k n = b (Fin.last n) := by
  simp [eLast, dotProduct_single]

theorem isUnit_one_add {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0) :
    IsUnit (1 + vecMulVec (eLast k n) b) := by
  rw [Matrix.isUnit_iff_isUnit_det, vecMulVec_eq (ι := Unit),
    det_one_add_replicateCol_mul_replicateRow, dotProduct_eLast]
  exact h.isUnit

theorem shearGL_mulVec {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0)
    (x : Fin (n + 1) → k) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x =
      x + (b ⬝ᵥ x) • eLast k n := by
  have e : ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
    unfold shearGL
    rw [dif_pos (isUnit_one_add b h)]
    rfl
  rw [e, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem dotProduct_shear {n : ℕ} (b x : Fin (n + 1) → k) :
    b ⬝ᵥ (x + (b ⬝ᵥ x) • eLast k n) = (1 + b (Fin.last n)) * (b ⬝ᵥ x) := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_eLast, smul_eq_mul]
  ring

theorem exists_bound {n : ℕ} (g : GL (Fin (n + 1)) k) :
    ∃ C : kˣ, 1 ≤ valuation k (C : k) ∧
      (∀ i, valuation k (((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) ≤ valuation k (C : k)) ∧
      ∀ i j, valuation k (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) ≤
        valuation k (C : k) := by
  let f : Option (Fin (n + 1) ⊕ Fin (n + 1) × Fin (n + 1)) → k := fun o =>
    match o with
    | none => 1
    | some (.inl i) => ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i
    | some (.inr p) => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p.1 p.2
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun o => valuation k (f o)
  have h1 : 1 ≤ valuation k (f i₀) := by simpa [f] using hi₀ none
  have hne : f i₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact absurd h1 (by simp)
  exact ⟨Units.mk0 _ hne, h1, fun i => hi₀ (some (.inl i)), fun i j => hi₀ (some (.inr (i, j)))⟩

theorem mul_mem_cball {a u : k} {p C t : kˣ} (hp : valuation k (p : k) ≤ 1)
    (ha : a ∈ cball (p * C⁻¹ * t)) (hu : valuation k u ≤ valuation k (C : k)) : a * u ∈ cball t := by
  have ha' : valuation k a ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := ha
  show valuation k (a * u) ≤ valuation k (t : k)
  calc valuation k (a * u) = valuation k a * valuation k u := map_mul _ _ _
    _ ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) * valuation k (C : k) := mul_le_mul' ha' hu
    _ = valuation k (p : k) * valuation k (t : k) := by
        rw [← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
    _ ≤ valuation k (t : k) := mul_le_of_le_one_left' hp

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  intro k _ _ _ _ n g
  obtain ⟨C, hC1, hu, hH⟩ := exists_bound g
  obtain ⟨p₀, hp0, hp1⟩ : ∃ p : k, p ≠ 0 ∧ valuation k p < 1 := Valuation.IsNontrivial.exists_lt_one
  obtain ⟨p, rfl⟩ : ∃ p : kˣ, (p : k) = p₀ := ⟨Units.mk0 _ hp0, rfl⟩
  have hCi : valuation k ((C⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ hC1
  have hr1 : valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) < 1 := by
    simp only [Units.val_mul, map_mul]
    exact lt_of_le_of_lt ((mul_le_of_le_one_right' hCi).trans (mul_le_of_le_one_right' hCi)) hp1
  refine ⟨p * C⁻¹ * C⁻¹, hr1, fun b hb t x => ?_⟩
  have hlast : valuation k (b (Fin.last n)) < 1 := lt_of_le_of_lt (hb (Fin.last n)) hr1
  have hone : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hlast
  have hne : 1 + b (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hone
    exact zero_ne_one hone
  rw [shearGL_mulVec b hne x]
  have hGS : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (x + (b ⬝ᵥ x) • eLast k n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
        (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) := by
    rw [mulVec_add, mulVec_smul]
  have hd : ∀ z : Fin (n + 1) → k, b ⬝ᵥ z =
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) := by
    intro z
    rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hw : b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈
      box (n + 1) (p * C⁻¹) := by
    intro j
    change ∑ i, b i * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j ∈ cball (p * C⁻¹)
    refine Finset.sum_induction _ (· ∈ cball (p * C⁻¹)) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
    have h1 : valuation k (b i) ≤ valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) := hb i
    show valuation k (b i * _) ≤ valuation k ((p * C⁻¹ : kˣ) : k)
    rw [map_mul]
    refine (mul_le_mul' h1 (hH i j)).trans (le_of_eq ?_)
    rw [← map_mul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hdot : ∀ y ∈ box (n + 1) t,
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ y ∈
        cball (p * C⁻¹ * t) := by
    intro y hy
    refine dotProduct_mem_cball (s := t) ?_ hy
    rwa [mul_inv_cancel_right]
  have hp : valuation k (p : k) ≤ 1 := hp1.le
  constructor
  · intro h i
    have h2 : (1 + b (Fin.last n)) * (b ⬝ᵥ x) ∈ cball (p * C⁻¹ * t) := by
      rw [← dotProduct_shear, hd (x + (b ⬝ᵥ x) • eLast k n)]
      exact hdot _ h
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      have h2' : valuation k ((1 + b (Fin.last n)) * (b ⬝ᵥ x)) ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := h2
      rw [map_mul, hone, one_mul] at h2'
      exact h2'
    rw [hGS] at h
    have e : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) i =
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
          (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n)) i +
        -((b ⬝ᵥ x) * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) := by
      simp
    rw [e]
    exact add_mem_cball (h i) (neg_mem_cball (mul_mem_cball hp h3 (hu i)))
  · intro h i
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      rw [hd x]
      exact hdot _ h
    rw [hGS]
    exact add_mem_cball (h i) (mul_mem_cball hp h3 (hu i))

end GlobalTheory.CompanionTheory.MirPair.ShearLat
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_preserves_box_membership : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MirPair.ShearLat.main
end

section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_box_integral_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ), Continuous ψ → HasConductor ψ c → ∀ (m : ℕ) (t : kˣ) (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ), IsCompact M → MeasurableSet M → Continuous f → (∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) → ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | exact GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | (intros; apply GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists <;> assumption)
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem JJ_preimage_box_eq_JJ_box : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB g v v'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hmono : ∀ {a a' : kˣ}, valuation k (a : k) ≤ valuation k (a' : k) →
      ∀ b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a, b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a' := by
    intro a a' haa' b hb
    have hb' : ∀ j, valuation k (b j) ≤ valuation k (a : k) := hb
    show ∀ j, valuation k (b j) ≤ valuation k (a' : k)
    exact fun j => le_trans (hb' j) haa'
  have hmin : ∀ a a' : kˣ, ∃ r : kˣ,
      valuation k (r : k) ≤ valuation k (a : k) ∧ valuation k (r : k) ≤ valuation k (a' : k) := by
    intro a a'
    rcases le_total (valuation k (a : k)) (valuation k (a' : k)) with h | h
    exacts [⟨a, le_rfl, h⟩, ⟨a', h, le_rfl⟩]
  obtain ⟨r₁, hr₁, h₁⟩ := GlobalTheory.T.shear_preserves_box_membership g
  obtain ⟨r₂, -, h₂⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₃, -, h₃⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T' hT' v'
  obtain ⟨r₄, h₄₁, h₄₂⟩ := hmin r₁ r₂
  obtain ⟨r, hr₄, hr₃⟩ := hmin r₄ r₃
  refine ⟨r, fun t ht t' hgt => ?_⟩
  set M : Set (Fin (n + 1) → k) :=
    {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'} with hM
  have hMimage : M = (fun y => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      *ᵥ y) '' (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t' : Set (Fin (n + 1) → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      show (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) ∈
          GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'
      simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, SetLike.mem_coe] using hy
  have hMc : IsCompact M := by
    rw [hMimage]
    exact (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) t').image
      (Continuous.matrix_mulVec continuous_const continuous_id)
  have hMm : MeasurableSet M := hMc.isClosed.measurableSet
  have hw : Continuous (GlobalTheory.CompanionTheory.MirPair.wt ψ n) := by
    unfold GlobalTheory.CompanionTheory.MirPair.wt
    exact continuous_subtype_val.comp (hψ.comp (continuous_apply (Fin.last n)).neg)
  have hf : Continuous fun x =>
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x :=
    hw.mul (GlobalTheory.T.mirabolic_coefficient_continuous T B hT v v')
  have hsub : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t : Set (Fin (n + 1) → k)) ⊆ M :=
    fun x hx => hgt x hx
  have key := GlobalTheory.T.fourier_box_integral_vanishing ν ψ c hψ hc (n + 1) t M
    (fun x => GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x)
    (GlobalTheory.CompanionTheory.MirPair.JJ ν ψ T B M v v') hMc hMm hf (by
      intro b hb
      have hbv : ∀ j, valuation k (b j) ≤ valuation k ((c * t⁻¹ : kˣ) : k) := hb
      have hb₁ := hmono (le_trans ht (le_trans hr₄ h₄₁)) b hb
      have hb₂ := hmono (le_trans ht (le_trans hr₄ h₄₂)) b hb
      have hb₃ := hmono (le_trans ht hr₃) b hb
      have hlast : valuation k (b (Fin.last n)) < 1 :=
        lt_of_le_of_lt (le_trans (hbv (Fin.last n)) (le_trans ht (le_trans hr₄ h₄₁))) hr₁
      have hinv : ∀ x, ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M :=
        fun x => h₁ b hb₁ t' x
      have h := GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hB b M v v'
        hlast (h₂ b hb₂) hinv
      rw [h₃ b hb₃] at h
      exact h)
  rw [Set.inter_eq_right.2 hsub] at key
  exact key.symm

end GlobalTheory.CompanionTheory.MirPair
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_bound : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box
end
