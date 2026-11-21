import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResRdApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponentStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpanned
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecMulAndConstTermMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn

section
section
namespace GlobalTheory

open Module

theorem relation_descends_along_functional (K A B : Type) [Field K] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B)
    (hrd : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f) (W : Submodule K A) [FiniteDimensional K W]
    (hW : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ W) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (φ : ℂ →+ K) (hφ : ∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c)
    {ι : Type} [Fintype ι] (x : ι → A) (hx : ∀ s, x s ∈ W) (c : ι → ℂ)
    (h : ∑ s, c s • rd (x s) = 0) : ∑ s, φ (c s) • x s = 0 := by
  classical
  obtain ⟨n, ⟨bW⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K W) := ⟨_, ⟨Module.finBasis K W⟩⟩
  have hli : LinearIndependent K (fun j => (bW j : A)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hli' := hW n (fun j => (bW j : A)) (fun j => (bW j).2) hli
  have hcoord : ∃ α : ι → Fin n → K, ∀ s, x s = ∑ j, α s j • (bW j : A) := by
    refine ⟨fun s j => bW.repr ⟨x s, hx s⟩ j, fun s => ?_⟩
    have h1 := congrArg (fun v : W => (v : A)) (bW.sum_repr ⟨x s, hx s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := hcoord
  have hrdx : ∀ s, rd (x s) = ∑ j, σ (α s j) • rd (bW j : A) := by
    intro s
    rw [hα s, map_sum]
    simp only [hrd]
  have hcoef : ∀ j, ∑ s, c s * σ (α s j) = 0 := by
    have h' : ∑ j, (∑ s, c s * σ (α s j)) • rd (bW j : A) = 0 := by
      rw [← h]
      simp only [hrdx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => Fintype.linearIndependent_iff.mp hli' _ h' j
  have hgoal : ∑ s, φ (c s) • x s = ∑ j, (∑ s, φ (c s) * α s j) • (bW j : A) := by
    simp only [hα, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hgoal]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h5 : ∑ s, φ (c s) * α s j = φ (∑ s, c s * σ (α s j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm (c s), hφ]
    exact mul_comm _ _
  rw [h5, hcoef j, map_zero, zero_smul]

theorem exists_functional_ne_zero_of_embedding (K : Type) [Field K] (σ : K →+* ℂ) (m : ℂ)
    (hm : m ≠ 0) : ∃ φ : ℂ →+ K, (∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c) ∧ φ m ≠ 0 := by
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual K ℂ, f m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hm ((Module.forall_dual_apply_eq_zero_iff K m).mp hcon)
  refine ⟨f.toAddMonoidHom, fun a c => ?_, hf⟩
  have hsmul : σ a * c = a • c := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  simp only [LinearMap.toAddMonoidHom_coe, hsmul, LinearMap.map_smul, smul_eq_mul]

theorem exists_rational_multiplier_of_complex :
    ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  classical
  intro K A B _ _ _ _ _ σ rd hrd V V' _ _ hVV h hspan hne
  have : FiniteDimensional K ↥(V * V') :=
    Module.Finite.iff_fg.mpr (Submodule.FG.mul (Module.Finite.iff_fg.mp inferInstance)
      (Module.Finite.iff_fg.mp inferInstance))
  have hrdsum : ∀ {m : ℕ} (a : Fin m → K) (v : Fin m → A),
      rd (∑ j, a j • v j) = ∑ j, σ (a j) • rd (v j) := by
    intro m a v
    rw [map_sum]
    simp only [hrd]
  have hexp : ∀ {U : Submodule K A} {m : ℕ} (b : Basis (Fin m) K U) (u : U),
      (u : A) = ∑ j, b.repr u j • (b j : A) := by
    intro U m b u
    have h1 := congrArg (fun v : U => (v : A)) (b.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨n, ⟨bV⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V) := ⟨_, ⟨Module.finBasis K V⟩⟩
  obtain ⟨n', ⟨bV'⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V') := ⟨_, ⟨Module.finBasis K V'⟩⟩
  have hC : ∀ i, ∃ C : Fin n' → ℂ, h * rd (bV i : A) = ∑ j, C j • rd (bV' j : A) := by
    intro i
    have hm := hspan _ (bV i).2
    have hsub : Submodule.span ℂ (rd '' (V' : Set A)) ≤
        Submodule.span ℂ (Set.range fun j => rd (bV' j : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      have e : u = ∑ j, bV'.repr ⟨u, hu⟩ j • (bV' j : A) := hexp bV' ⟨u, hu⟩
      rw [e, hrdsum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨C, hCe⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hsub hm)
    exact ⟨C, hCe.symm⟩
  choose C hC using hC
  have hi0 : ∃ i, h * rd (bV i : A) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨f, hf, hfne⟩ := hne
    apply hfne
    have e : f = ∑ j, bV.repr ⟨f, hf⟩ j • (bV j : A) := hexp bV ⟨f, hf⟩
    rw [e, hrdsum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, hcon i, smul_zero]
  obtain ⟨i0, hi0⟩ := hi0
  have hj0 : ∃ j, C i0 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hi0
    rw [hC i0]
    exact Finset.sum_eq_zero fun j _ => by rw [hcon j, zero_smul]
  obtain ⟨j0, hj0⟩ := hj0
  obtain ⟨φ, hφ, hφne⟩ := exists_functional_ne_zero_of_embedding K σ (C i0 j0) hj0
  obtain ⟨T, hT⟩ : ∃ T : V →ₗ[K] V', ∀ i, T (bV i) = ∑ j, φ (C i j) • bV' j :=
    ⟨bV.constr K (fun i => ∑ j, φ (C i j) • bV' j), fun i => bV.constr_basis K _ i⟩
  have hTA : ∀ i, ((T (bV i) : V') : A) = ∑ j, φ (C i j) • (bV' j : A) := by
    intro i
    rw [hT]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hbasis : ∀ i k, ((T (bV i) : V') : A) * (bV k : A) = (bV i : A) * ((T (bV k) : V') : A) := by
    intro i k
    have key := relation_descends_along_functional K A B σ rd hrd (V * V') hVV φ hφ
      (ι := Fin n' ⊕ Fin n')
      (Sum.elim (fun j => (bV k : A) * (bV' j : A)) (fun j => (bV i : A) * (bV' j : A)))
      (by
        rintro (j | j)
        · exact Submodule.mul_mem_mul (bV k).2 (bV' j).2
        · exact Submodule.mul_mem_mul (bV i).2 (bV' j).2)
      (Sum.elim (fun j => C i j) (fun j => - C k j))
      (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, map_mul, neg_smul, Finset.sum_neg_distrib]
        simp only [← mul_smul_comm, ← Finset.mul_sum, ← hC]
        ring)
    rw [Fintype.sum_sum_type] at key
    simp only [Sum.elim_inl, Sum.elim_inr, map_neg, neg_smul, Finset.sum_neg_distrib,
      ← mul_smul_comm, ← Finset.mul_sum] at key
    rw [hTA, hTA, mul_comm _ ((bV k : V) : A)]
    rw [mul_neg] at key
    exact add_neg_eq_zero.mp key
  have hleft : ∀ i (g : V), ((T (bV i) : V') : A) * (g : A) = (bV i : A) * ((T g : V') : A) := by
    intro i g
    have h2 := bV.ext (f₁ := (LinearMap.mulLeft K ((T (bV i) : V') : A)).comp V.subtype)
      (f₂ := (LinearMap.mulLeft K ((bV i : V) : A)).comp (V'.subtype.comp T))
      (fun k => by simpa using hbasis i k)
    simpa using LinearMap.congr_fun h2 g
  refine ⟨T, ?_, fun f g => ?_⟩
  · intro hT0
    have h1 : T (bV i0) = 0 := by rw [hT0, LinearMap.zero_apply]
    rw [hT] at h1
    exact hφne (Fintype.linearIndependent_iff.mp bV'.linearIndependent _ h1 j0)
  · have h2 := bV.ext (f₁ := (LinearMap.mulRight K (g : A)).comp (V'.subtype.comp T))
      (f₂ := (LinearMap.mulRight K ((T g : V') : A)).comp V.subtype)
      (fun i => by simpa using hleft i g)
    simpa using LinearMap.congr_fun h2 f

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  atlas_forward_decl GlobalTheory.exists_rational_multiplier_of_complex
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  first | exact @GlobalTheory.FlatCore.cuspOn_fd_and_span_rdU | exact GlobalTheory.FlatCore.cuspOn_fd_and_span_rdU | (intros; apply GlobalTheory.FlatCore.cuspOn_fd_and_span_rdU <;> assumption)
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatShift

theorem flat_step {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) (ρ : E →+* ℂ) (i j : ℕ) (hi : i < Dw.mult ρ) (hj : j < Dw.mult ρ) :
    (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = (wtOf Dw (flatWt Dw τ) 0).1 (ρ, j) ∧
      -1 ≤ (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) := by
  simp only [wtOf, flatWt, parWt, Datum.mult] at hi hj ⊢
  split_ifs at hi hj ⊢ <;> omega

theorem exists_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  intro E _ _ _ H Dw a n τ hD ha
  refine ⟨fun x => if x.2 < Dw.mult x.1 then ((a x : ℤ) + (wtOf Dw (flatWt Dw τ) 0).1 x).toNat else 0,
    ⟨fun ρ i j hij => ?_, hD.2⟩, fun ρ i hi => ?_, ?_⟩
  · by_cases hj : j < Dw.mult ρ
    · have hi : i < Dw.mult ρ := lt_of_le_of_lt hij hj
      have h1 : a (ρ, j) ≤ a (ρ, i) := hD.1 ρ hij
      obtain ⟨e, -⟩ := flat_step Dw τ ρ i j hi hj
      simp only [if_pos hi, if_pos hj]
      omega
    · simp only [if_neg hj]; exact Nat.zero_le _
  · have h1 := ha ρ i hi
    have h2 := (flat_step Dw τ ρ i i hi hi).2
    simp only [if_pos hi]
    omega
  · funext x
    rcases x with _ | ⟨ρ, i⟩
    · simp [exZ, wtZ, wtOf_snd]
    · have h1 := ha ρ i i.2
      have h2 := (flat_step Dw τ ρ i i i.2 i.2).2
      simp only [exZ, wtZ, Prod.fst_add, Pi.add_apply, if_pos i.2]
      omega

end GlobalTheory.FlatShift
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_weight_shift_flatLineDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  first | exact @GlobalTheory.FlatShift.exists_shift | exact GlobalTheory.FlatShift.exists_shift | (intros; apply GlobalTheory.FlatShift.exists_shift <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.HorizMul

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_zpow (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (m : ℤ) (x : Frame X.Ψ r) :
    X.pnorm (m • la) (fun y => P y ^ m) x = X.pnorm la P x ^ m := by
  unfold Data.pnorm
  rw [mul_zpow, norm_zpow, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem differentiable_matDet {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Differentiable ℂ fun y : Frame Ψ r => (mat y τ).det := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem horizGen_rmul' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (x b : Frame Ψ r) :
    horizGen τ (rmul x b) = horizGen τ x * horizGen τ b := by
  show (mat x τ * mat b τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv]
  rfl

theorem horizGen_lact' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (γ : GL (Fin r) E) (x : Frame Ψ r) :
    horizGen τ (lact γ x) = (τ.1 γ.1.det)⁻¹ * horizGen τ x := by
  show (γ.1.map τ.1 * mat x τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv, RingHom.map_det]
  rfl

theorem bchar_zsmul_modelFlat {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (m : ℤ) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) :
    bchar (m • modelFlat r τ) b = horizGen τ b ^ m := by
  classical
  have hd : (mat b τ).det = ∏ i, b τ i i :=
    Matrix.det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
  unfold bchar
  rw [Finset.prod_eq_single τ (fun τ' _ h => by simp [modelFlat, h]) (by simp)]
  simp only [Pi.smul_apply, modelFlat, if_true, smul_eq_mul, mul_neg, mul_one]
  rw [Finset.prod_zpow, horizGen, hd, inv_zpow', zpow_neg]

theorem isBddSec_horizGen_zpow (X : Data E r) (τ : X.Ψ) (m : ℤ)
    (hdet : ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) (hχ : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1) :
    X.IsBddSec (m • modelFlat r τ) fun y => horizGen τ y ^ m := by
  refine ⟨⟨fun y hy => ?_, fun x _ b hb => ?_, fun γ hγ x _ => ?_⟩, Real.sqrt ‖τ.1 X.Gm.det‖ ^ m, fun y hy => ?_⟩
  · have hne : (mat y τ).det ≠ 0 := (hy τ).1
    exact (((differentiable_matDet τ y).inv hne).zpow (Or.inl (inv_ne_zero hne))).differentiableWithinAt
  · beta_reduce
    rw [horizGen_rmul', mul_zpow, bchar_zsmul_modelFlat τ m hb, mul_comm]
  · beta_reduce
    rw [horizGen_lact', hdet γ hγ, map_one, inv_one, one_mul, hχ γ hγ, one_mul]
  · rw [pnorm_zpow, pnorm_horizGen X τ hy]

theorem chi_zsmul_modelFlat (X : Data E r) (τ : X.Ψ) (la : Wt X.Ψ r) (m : ℤ)
    (hχ : ∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1 := by
  intro γ hγ
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h0 : X.χ la γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h1 := (X.χ_add la (m • modelFlat r τ) γ hγ).symm.trans (hχ γ hγ)
  exact mul_left_cancel₀ h0 (h1.trans (mul_one _).symm)

theorem horizGen_zpow_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (τ : X.Ψ)
    (la : Wt X.Ψ r) (m : ℤ), (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) →
    (∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) →
    ∀ P ∈ X.SS la, (fun y => horizGen τ y ^ m * P y) ∈ X.SS (la + m • modelFlat r τ) := by
  intro E _ _ _ r X τ la m hdet hχ P hP
  have hQ := isBddSec_horizGen_zpow X τ m hdet (chi_zsmul_modelFlat X τ la m hχ)
  obtain ⟨hb, hfj⟩ := GlobalTheory.bddSec_mul_and_constTerm_mul E r X la _ P _ hP.1 hQ
  have e : (fun y => horizGen τ y ^ m * P y) = P * fun y => horizGen τ y ^ m := funext fun y => mul_comm _ _
  rw [e]
  refine ⟨hb, fun ξ hξ x hx => ?_⟩
  rw [hfj ξ hξ x hx, hP.2 ξ hξ x hx, zero_mul]

end GlobalTheory.FlatCore.HorizMul
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.MulSpan

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zero_mem_SS' (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  refine ⟨⟨⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩, 0, fun x _ => by
    simp [Data.pnorm]⟩, fun ξ _ x _ => ?_⟩
  unfold Data.fj
  split_ifs <;> simp

open Classical in

def mulAt {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) : FDSec X →ₗ[ℂ] FDSec X :=
  (LinearMap.single ℂ (fun k => Frame (X k).Ψ r → ℂ) k0) ∘ₗ (LinearMap.mulLeft ℂ h) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) k0)

theorem mulAt_same {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) :
    mulAt X k0 h P k0 = fun y => h y * P k0 y := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same, LinearMap.mulLeft_apply,
    LinearMap.proj_apply]
  rfl

open Classical in
theorem mulAt_ne {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) {k : Comp}
    (hk : k ≠ k0) : mulAt X k0 h P k = 0 := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_of_ne hk]

theorem mulAt_mem_holSub {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ)
    (la la' : ∀ k, Wt (X k).Ψ r) (hh : ∀ Q ∈ (X k0).SS (la k0), (fun y => h y * Q y) ∈ (X k0).SS (la' k0))
    {P : FDSec X} (hP : P ∈ holSub X la) : mulAt X k0 h P ∈ holSub X la' := by
  have hle : holSub X la ≤ (holSub X la').comap (mulAt X k0 h) := by
    refine Submodule.span_le.2 fun Q hQ => ?_
    refine Submodule.subset_span (s := {P | IsHolCusp X la' P}) fun k => ?_
    by_cases hk : k = k0
    · subst hk
      rw [mulAt_same]
      exact hh _ (hQ k)
    · rw [mulAt_ne X k0 h Q hk]
      exact zero_mem_SS' _ _
  exact hle hP

theorem horizGen_zpow_mul_rdU_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z σ hσ k0 hk τ' m b b' n hb hb' hpos hn hw f hf
  have hP : rdU (U σ) f ∈ holSub (U σ).X (modelWt (U σ) (wtZ b n)) := (mem_cuspW.1 (cuspOn_le U Z _ hf)).2 σ hσ
  have hLP : mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) ∈
      holSub (U σ).X (modelWt (U σ) (wtZ b' n)) := by
    refine mulAt_mem_holSub _ k0 _ _ _ (fun Q hQ => ?_) hP
    rw [hw]
    refine HorizMul.horizGen_zpow_mul_mem_SS E r _ τ' _ m (hL.det σ hσ k0) (fun γ hγ => ?_) Q hQ
    rw [← hw, modelWt_wtZ, modelWt_wtZ, hL.chi σ hσ b n hb k0 γ hγ, hL.chi σ hσ b' n hb' k0 γ hγ]
  have hoff : ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k y = 0 := by
    intro k y hy
    by_cases hkk : k = k0
    · subst hkk
      have hd : y ∉ ((U σ).X k).dom := fun hd => hy (by rw [hk]; exact ⟨rfl, hd⟩)
      have h0 : rdU (U σ) f k y = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_neg, not_false_eq_true]
      rw [mulAt_same]
      simp only [h0, mul_zero]
    · rw [mulAt_ne _ _ _ _ hkk]
      rfl
  have hsp := (cuspOn_fd_and_span_rdU E H Dw l Xo c r U x hL Z σ hσ b' n hb' hpos hn).2 _ hLP hoff
  let R : FDSec (U σ).X →ₗ[ℂ] (↥((U σ).X k0).dom → ℂ) :=
    { toFun := fun Q y => Q k0 y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmap := Submodule.mem_map_of_mem (f := R) hsp
  rw [Submodule.map_span, Set.image_image] at hmap
  have e : R (mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f)) =
      fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1 := by
    funext y
    show mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k0 y.1 = _
    rw [mulAt_same]
  rw [e] at hmap
  exact hmap

end GlobalTheory.FlatCore.MulSpan
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  first | exact @GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span | exact GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span | (intros; apply GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span <;> assumption)
end

section
namespace GlobalTheory.FlatPair

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem holAlg_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  intro E _ _ _ r X hne
  obtain ⟨y0, hy0⟩ := hne
  haveI : Nontrivial (holAlg X) := ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg Subtype.val h) ⟨y0, hy0⟩
    simp at this⟩⟩
  haveI : NoZeroDivisors (holAlg X) := ⟨fun {a b} hab => by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨F, hF, hFa⟩ := a.2
    obtain ⟨G, hG, hGb⟩ := b.2
    have ha' : ∃ y : X.dom, (a : X.dom → ℂ) y ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (Subtype.ext (funext h))
    obtain ⟨y, hy⟩ := ha'
    have hfg : ∀ w ∈ X.dom, F w * G w = 0 := by
      intro w hw
      have := congrFun (congrArg Subtype.val hab) ⟨w, hw⟩
      rw [← hFa ⟨w, hw⟩, ← hGb ⟨w, hw⟩]
      simpa using this
    have hFy : F y.1 ≠ 0 := by rw [← hFa y]; exact hy
    have key := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hF hG hfg y.2 hFy
    apply hb
    apply Subtype.ext
    funext z
    rw [hGb z]
    simpa using key z.1 z.2⟩
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FlatPair
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  first | exact @GlobalTheory.FlatPair.holAlg_isDomain | exact GlobalTheory.FlatPair.holAlg_isDomain | (intros; apply GlobalTheory.FlatPair.holAlg_isDomain <;> assumption)
end

section
namespace GlobalTheory

theorem commuting_map_eq_smul_multiplier :
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] (W W' : Submodule ℂ B) [FiniteDimensional ℂ W] (h h' : B), h * h' = 1 → (∀ w ∈ W', h' * w ∈ W) → ∀ T : W →ₗ[ℂ] W', T ≠ 0 → (∀ f g : W, (T f : B) * (g : B) = (f : B) * (T g : B)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : W, (T f : B) = a • (h * (f : B)) := by
  intro B _ _ _ W W' _ h h' hhh hW T hT hcomm
  let S : W →ₗ[ℂ] W :=
    { toFun := fun f => ⟨h' * (T f : B), hW _ (T f).2⟩
      map_add' := fun f g => by ext; simp [mul_add]
      map_smul' := fun c f => by ext; simp [mul_smul_comm] }
  haveI : Nontrivial W := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hT
    ext f
    rw [Subsingleton.elim f 0]
    simp
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue S
  obtain ⟨f₀, hf₀⟩ := ha.exists_hasEigenvector
  have hS : S f₀ = a • f₀ := hf₀.apply_eq_smul
  have h0 : (T f₀ : B) = a • (h * (f₀ : B)) := by
    have hc : h' * (T f₀ : B) = a • (f₀ : B) := by
      have := congrArg (fun x : W => (x : B)) hS
      simpa [S] using this
    calc (T f₀ : B) = h * (h' * T f₀) := by rw [← mul_assoc, hhh, one_mul]
    _ = h * (a • (f₀ : B)) := by rw [hc]
    _ = a • (h * (f₀ : B)) := mul_smul_comm _ _ _
  have hf0ne : (f₀ : B) ≠ 0 := by
    intro hz
    exact hf₀.2 (Subtype.ext hz)
  have key : ∀ f : W, (T f : B) = a • (h * (f : B)) := by
    intro f
    have hx := hcomm f f₀
    rw [h0] at hx
    apply mul_right_cancel₀ hf0ne
    rw [hx]
    simp only [Algebra.smul_def]
    ring
  refine ⟨a, ?_, key⟩
  rintro rfl
  apply hT
  ext f
  simp [key f]

end GlobalTheory
end

section
namespace GlobalTheory

theorem commuting_multiplier_eq_const_smul_generator
    (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B]
    (σ : K →+* ℂ) (rd : A →+* B)
    (hsemi : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f)
    (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A)
    [FiniteDimensional K V] [FiniteDimensional K V']
    (hV : ∀ f ∈ V, rd f ∈ R) (hV' : ∀ f ∈ V', rd f ∈ R)
    (hind : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (hind' : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (h h' : B) (hh : h ∈ R) (hh' : h' ∈ R) (hhh : h * h' = 1)
    (hsub : ∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A)))
    (T : V →ₗ[K] V') (hT : T ≠ 0)
    (hcomm : ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  classical
  have expand : ∀ (U : Submodule K A) [FiniteDimensional K U] (f : U),
      rd (f : A) = ∑ j, σ ((Module.finBasis K U).repr f j) •
        rd ((Module.finBasis K U j : U) : A) := by
    intro U _ f
    conv_lhs => rw [← (Module.finBasis K U).sum_repr f]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hsemi]
  set bV := Module.finBasis K V with hbV
  set bV' := Module.finBasis K V' with hbV'
  let gV : Fin (Module.finrank K V) → R := fun j => ⟨rd (bV j : A), hV _ (bV j).2⟩
  let gV' : Fin (Module.finrank K V') → R := fun j => ⟨rd (bV' j : A), hV' _ (bV' j).2⟩
  have liV : LinearIndependent ℂ gV := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind _ (fun j => (bV j : A)) (fun j => (bV j).2)
      (bV.linearIndependent.map' V.subtype V.ker_subtype)
  have liV' : LinearIndependent ℂ gV' := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind' _ (fun j => (bV' j : A)) (fun j => (bV' j).2)
      (bV'.linearIndependent.map' V'.subtype V'.ker_subtype)
  let W := Submodule.span ℂ (Set.range gV)
  let W' := Submodule.span ℂ (Set.range gV')
  have eqV : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) = ∑ j, σ (bV.repr f j) • gV j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV]
    exact expand V f
  have eqV' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) = ∑ j, σ (bV'.repr f j) • gV' j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV']
    exact expand V' f
  have memW : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) ∈ W := by
    intro f
    rw [eqV f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have memW' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) ∈ W' := by
    intro f
    rw [eqV' f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW : Module.Basis (Fin (Module.finrank K V)) ℂ W := Module.Basis.span liV
  have bW_apply : ∀ j, (bW j : R) = gV j := fun j => congrArg Subtype.val (Module.Basis.span_apply liV j)
  let img : Fin (Module.finrank K V) → W' := fun j => ⟨⟨rd (T (bV j) : A), hV' _ (T (bV j)).2⟩, memW' (T (bV j))⟩
  let Tc : W →ₗ[ℂ] W' := bW.constr ℂ img
  have Tc_rd : ∀ f : V, Tc ⟨⟨rd f, hV _ f.2⟩, memW f⟩ = ⟨⟨rd (T f : A), hV' _ (T f).2⟩, memW' (T f)⟩ := by
    intro f
    have e1 : (⟨⟨rd f, hV _ f.2⟩, memW f⟩ : W) = ∑ j, σ (bV.repr f j) • bW j := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, bW_apply]
      exact eqV f
    rw [e1, map_sum]
    simp only [map_smul, Tc, Module.Basis.constr_basis]
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finset_sum,
      SetLike.val_smul, img]
    conv_rhs => rw [← bV.sum_repr f]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsemi]
  have Tc_basis : ∀ i, Tc (bW i) = img i := fun i => by
    simp only [Tc, Module.Basis.constr_basis]
  haveI : FiniteDimensional ℂ W := Module.Finite.of_basis bW
  have Tc_ne : Tc ≠ 0 := by
    obtain ⟨f, hf⟩ : ∃ f, T f ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hT (LinearMap.ext hc)
    have hfA : (T f : A) ≠ 0 := fun hz => hf (Subtype.ext hz)
    have li1 : LinearIndependent ℂ (fun _ : Fin 1 => rd (T f : A)) :=
      hind' 1 (fun _ => (T f : A)) (fun _ => (T f).2)
        (linearIndependent_unique_iff.mpr hfA)
    have hne : rd (T f : A) ≠ 0 := li1.ne_zero 0
    intro h0
    apply hne
    have := congrArg (fun x : W' => ((x : R) : B)) (Tc_rd f)
    simp only [h0, LinearMap.zero_apply] at this
    simpa using this.symm
  have spanLe : Submodule.span ℂ (rd '' (V : Set A)) ≤ W.map R.val.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨rd f, hV _ hf⟩, memW ⟨f, hf⟩, rfl⟩
  have hW'W : ∀ w ∈ W', (⟨h', hh'⟩ : R) * w ∈ W := by
    intro w hw
    have hle : W' ≤ W.comap (LinearMap.mulLeft ℂ (⟨h', hh'⟩ : R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (⟨h', hh'⟩ : R) * gV' i ∈ W
      obtain ⟨z, hz, hzeq⟩ := spanLe (hsub _ (bV' i).2)
      have : z = (⟨h', hh'⟩ : R) * gV' i := Subtype.ext hzeq
      rw [← this]; exact hz
    exact hle hw
  have hcommTc : ∀ x y : W, ((Tc x : R)) * (y : R) = (x : R) * (Tc y : R) := by
    let B1 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ (W'.subtype ∘ₗ Tc) W.subtype
    let B2 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ W.subtype (W'.subtype ∘ₗ Tc)
    have hB : B1 = B2 := by
      refine bW.ext fun i => bW.ext fun j => ?_
      simp only [B1, B2, LinearMap.compl₁₂_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mul_apply', Tc_basis, bW_apply]
      apply Subtype.ext
      simp only [img, gV, Subalgebra.coe_mul, ← map_mul]
      rw [hcomm]
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simpa [B1, B2] using this
  have hhhR : (⟨h, hh⟩ : R) * ⟨h', hh'⟩ = 1 := Subtype.ext (by simpa using hhh)
  obtain ⟨a, ha, hkey⟩ := commuting_map_eq_smul_multiplier R W W' ⟨h, hh⟩ ⟨h', hh'⟩ hhhR hW'W Tc Tc_ne hcommTc
  refine ⟨a, ha, fun f => ?_⟩
  have := congrArg Subtype.val (hkey ⟨⟨rd f, hV _ f.2⟩, memW f⟩)
  rw [Tc_rd] at this
  simpa using this

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ f ∈ V, rd f ∈ R) → (∀ f ∈ V', rd f ∈ R) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h h' : B, h ∈ R → h' ∈ R → h * h' = 1 → (∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A))) → ∀ T : V →ₗ[K] V', T ≠ 0 → (∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  first | exact @GlobalTheory.commuting_multiplier_eq_const_smul_generator | exact GlobalTheory.commuting_multiplier_eq_const_smul_generator | (intros; apply GlobalTheory.commuting_multiplier_eq_const_smul_generator <;> assumption)
end

section
noncomputable section
namespace GlobalTheory.FlatPair
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section Lemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_mem {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H) (k : V.Comp) :
    relab c σ τ.1 ∈ (V.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (by
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)

theorem modelWt_shift {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H)
    {G G' : WTZ E} (hG : Even G.2) (h : exZ Dw G' = exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) (k : V.Comp)
    (hτ : relab c σ τ.1 ∈ (V.X k).Ψ) : modelWt V G' k = modelWt V G k + modelFlat r ⟨_, hτ⟩ := by
  rw [modelWt_congr V hσ hU h, modelWt_add V hG (even_wtOf _ _), modelWt_flatWt V hσ hU τ k hτ]

theorem cuspOn_congr {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c)
    {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : cuspOn U Z G = cuspOn U Z G' := by
  ext f
  simp only [cuspOn, Submodule.mem_inf, mem_cuspW, h]
  refine and_congr_left fun _ => and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem res_indep {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (Z : Comp Xo c)
    (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (k0 : (U σ).Comp)
    (hk : framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom}) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → (∀ i, b i ∈ suppOn Z) →
      LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => fun y : ↥((U σ).X k0).dom => rdU (U σ) (b i) k0 y.1)) ∧
    ∀ f ∈ sec Xo c a n, f ∈ suppOn Z → f ≠ 0 → ∃ y : ↥((U σ).X k0).dom, rdU (U σ) f k0 y.1 ≠ 0 := by
  have hR := GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ H Dw l Xo c σ r
    (Formalism.L2.PjFree.Unf.ofPj (U σ)) (hL.unf σ hσ) a n
  simp only [Formalism.L2.PjFree.rdU_ofPj] at hR
  have hoff : ∀ f ∈ suppOn Z, ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      rdU (U σ) f k y = 0 := fun f hf k y hz => rdU_eq_zero (U σ) hf hz
  refine ⟨fun m b hb hs hli => ?_, fun f hf hs hne => ?_⟩
  · have h0 : LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := hR.1 m b hb hli
    rw [Fintype.linearIndependent_iff] at h0 ⊢
    intro w hw
    refine h0 w ?_
    funext k y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy⟩ := hz
      have := congrFun hw ⟨y, hy⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    · exact Finset.sum_eq_zero fun i _ => by rw [hoff _ (hs i) k y hz, mul_zero]
  · by_contra hall
    push_neg at hall
    refine hne (hR.2 f hf fun k y hy => ?_)
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy'⟩ := hz
      exact hall ⟨y, hy'⟩
    · exact hoff f hs k y hz

theorem horizGen_mem (X : Data E r) (τ : X.Ψ) :
    (fun y : ↥X.dom => horizGen τ y.1) ∈ holAlg X ∧ (fun y : ↥X.dom => (horizGen τ y.1)⁻¹) ∈ holAlg X ∧
      ∀ y ∈ X.dom, horizGen τ y ≠ 0 := by
  have hdet : Differentiable ℂ (fun y : Frame X.Ψ r => (mat y τ).det) := by
    have e : (fun y : Frame X.Ψ r => (mat y τ).det) =
        fun y => ∑ p : Equiv.Perm (Fin r), ((Equiv.Perm.sign p : ℤ) : ℂ) * ∏ i, y τ (p i) i := by
      funext y
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [e]
    fun_prop
  have hne : ∀ y ∈ X.dom, (mat y τ).det ≠ 0 := fun y hy => (hy τ).1
  refine ⟨⟨fun y => horizGen τ y, ?_, fun y => rfl⟩, ⟨fun y => (horizGen τ y)⁻¹, ?_, fun y => rfl⟩,
    fun y hy => inv_ne_zero (hne y hy)⟩
  · exact (hdet.differentiableOn).inv hne
  · have : (fun y => (horizGen τ y)⁻¹) = fun y : Frame X.Ψ r => (mat y τ).det := by
      funext y; simp [horizGen]
    rw [this]; exact hdet.differentiableOn

theorem resRd_mem_holAlg {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (σ : c.F →+* ℂ) (hσ : GoodEmb c σ)
    (hT : AllTest Xo c) (k : (U σ).Comp) (G : WTZ E) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) :
    resRd (U σ) hT k f ∈ holAlg ((U σ).X k) := by
  have h1 := (mem_cuspW.1 hf).2 σ hσ
  have h2 : ∀ P ∈ holSub (U σ).X (modelWt (U σ) G), DifferentiableOn ℂ (P k) ((U σ).X k).dom := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem P hP => exact (hP k).1.1.1
    | zero => exact differentiableOn_const 0
    | add P Q _ _ hP hQ => exact hP.add hQ
    | smul a P _ hP => exact (differentiableOn_const a).mul hP
  exact ⟨rdU (U σ) f k, h2 _ h1, fun y => rfl⟩

end Lemmas

theorem flat_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧
      f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨a, n, hD, h2, hn, f0, hf0, hf0ne⟩ := GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component E H Dw l Xo c r U x hL Z
  obtain ⟨a', hD', h1', hex⟩ := GlobalTheory.T.exists_dominant_weight_shift_flatLineDet E H Dw a n τ hD h2
  have h1 : ∀ ρ i, i < Dw.mult ρ → 1 ≤ a (ρ, i) := fun ρ i hi => le_trans (by norm_num) (h2 ρ i hi)
  have hT : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
  have hEv : Even (wtZ a n).2 := by
    obtain ⟨m, hm⟩ := hD.2
    exact ⟨m, by simp [wtZ, hm]⟩
  have hVV' : cuspOn U Z (wtZ a' n) = cuspOn U Z (wtZ a n + wtOf Dw (flatWt Dw τ) 0) :=
    cuspOn_congr hL.unf Z hex

  have hsec : ∀ (b : (E →+* ℂ) × ℕ → ℕ), cuspOn U Z (wtZ b n) ≤ sec Xo c b n := fun b f hf => by
    have := cuspW_le_secZ (U := U) (wtZ b n) (cuspOn_le U Z _ hf)
    rwa [AllWt.exZ_wtZ, secZ_nat] at this
  have hsupp : ∀ (G : WTZ E), cuspOn U Z G ≤ suppOn Z := fun G => inf_le_right
  have pk : ∀ σ, GoodEmb c σ → ∃ (k0 : (U σ).Comp) (hτ : relab c σ τ.1 ∈ ((U σ).X k0).Ψ),
      framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} ∧
      (∀ f ∈ cuspOn U Z (wtZ a n), (fun y : ↥((U σ).X k0).dom => horizGen ⟨_, hτ⟩ y.1) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a' n) : Set (Rul Xo c)))) ∧
      (∀ f ∈ cuspOn U Z (wtZ a' n), (fun y : ↥((U σ).X k0).dom => (horizGen ⟨_, hτ⟩ y.1)⁻¹) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c)))) := by
    intro σ hσ
    obtain ⟨k0, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
    have hτ := relab_mem (U σ) hσ (hL.unf σ hσ) τ k0
    have hw := modelWt_shift (U σ) hσ (hL.unf σ hσ) τ hEv hex k0 hτ
    refine ⟨k0, hτ, hk, fun f hf => ?_, fun f hf => ?_⟩
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ 1 a a' n hD hD' h1' hn (by rw [hw, one_smul]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ (-1) a' a n hD' hD h1 hn
        (by rw [hw, neg_one_smul, add_neg_cancel_right]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
  obtain ⟨σ0, hσ0⟩ : ∃ σ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a n hD h1 hn).1
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a' n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a' n hD' h1' hn).1
  have hprod : ∀ f ∈ cuspOn U Z (wtZ a n), ∀ g ∈ cuspOn U Z (wtZ a' n),
      f * g ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := by
    intro f hf g hg
    have e : exZ Dw (wtZ (a + a') (n + n)) = exZ Dw (wtZ a n) + exZ Dw (wtZ a' n) := by
      rw [wtZ_add]; funext i; exact exZ_add _ _ i
    have hm := mul_mem_secZ (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hf))
      (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hg))
    rw [← e, AllWt.exZ_wtZ, secZ_nat] at hm
    refine ⟨hm, ?_⟩
    rw [mul_comm]
    exact mul_mem_suppOn g (hsupp _ hf)
  obtain ⟨k0, hτ0, hk0, hA0, -⟩ := pk σ0 hσ0
  obtain ⟨T, hT0, hTc⟩ := GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier c.F (Rul Xo c) (↥((U σ0).X k0).dom → ℂ) σ0 (resRd (U σ0) hT k0)
    (resRd_smul (U σ0) hT k0) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun m b hb hli => by
      have hb' : ∀ i, b i ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := fun i =>
        (Submodule.mul_le.2 hprod) (hb i)
      exact (res_indep hL Z σ0 hσ0 k0 hk0 (a + a') (n + n)).1 m b (fun i => (hb' i).1) (fun i => (hb' i).2) hli)
    (fun y => horizGen ⟨_, hτ0⟩ y.1) hA0 ⟨f0, hf0, fun h0 => by
      obtain ⟨y, hy⟩ := (res_indep hL Z σ0 hσ0 k0 hk0 a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
      have := congrFun h0 y
      simp only [Pi.mul_apply, resRd_apply, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h | h
      · exact (horizGen_mem _ _).2.2 y.1 y.2 h
      · exact hy h⟩
  refine ⟨wtZ a n, f0, T ⟨f0, hf0⟩, hEv, hf0, hVV' ▸ (T ⟨f0, hf0⟩).2, hf0ne, fun σ hσ => ?_⟩
  obtain ⟨k1, hτ, hk, hA, hA'⟩ := pk σ hσ
  obtain ⟨y0, -⟩ := (res_indep hL Z σ hσ k1 hk a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
  haveI := GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain E r ((U σ).X k1) ⟨y0.1, y0.2⟩
  obtain ⟨hh, hh', hne⟩ := horizGen_mem ((U σ).X k1) ⟨_, hτ⟩
  obtain ⟨α, hα, hαT⟩ := GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt c.F (Rul Xo c) (↥((U σ).X k1).dom → ℂ) σ (resRd (U σ) hT k1)
    (resRd_smul _ _ _) (holAlg ((U σ).X k1)) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a n).1 m b (fun i => hsec a (hb i)) (fun i => hsupp _ (hb i)) hli)
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a' n).1 m b (fun i => hsec a' (hb i)) (fun i => hsupp _ (hb i))
      hli)
    _ _ hh hh' (by funext y; exact mul_inv_cancel₀ (hne y.1 y.2)) hA' T hT0 hTc
  refine ⟨α, hα, fun k hτk y hy => ?_⟩
  rw [hk] at hy
  obtain ⟨rfl, hyd⟩ := hy
  have e := congrFun (hαT ⟨f0, hf0⟩) ⟨y, hyd⟩
  simp only [resRd_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e
  rw [e]
  ring

end GlobalTheory.FlatPair
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_pair_quotient_horizontal_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧ f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  first | exact @GlobalTheory.FlatPair.flat_pair | exact GlobalTheory.FlatPair.flat_pair | (intros; apply GlobalTheory.FlatPair.flat_pair <;> assumption)
end
