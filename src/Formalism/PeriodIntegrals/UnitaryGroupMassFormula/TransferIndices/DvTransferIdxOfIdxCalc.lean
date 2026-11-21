import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.BlockHyp
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf

section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Side

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ} {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V}
  {Γ : Matrix (Fin n) (Fin n) K}

theorem BlockHyp.side (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (H : BlockHyp X Y Φ Ψ Γ)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hLsp : Submodule.span K (L : Set V) = ⊤)
    (hΦL : ∀ i, ∀ x ∈ L, x ∈ X → Φ i x ∈ L) (hΨL : ∀ j, ∀ y ∈ L, y ∈ Y → Ψ j y ∈ L) :
    (latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K)) ≤
        L ⊓ Y.restrictScalars (𝓞 K) ∧
      Submodule.span K (((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map
        ((Φt Φ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = Y ∧
      0 ≤ idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ∧
      idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ≤
        (Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) : ℤ) * vAdd w Γ.det := by
  set LX := L ⊓ X.restrictScalars (𝓞 K) with hLXd
  set LY := L ⊓ Y.restrictScalars (𝓞 K) with hLYd
  have hLX : Submodule.span K (LX : Set V) = X := cut_span L hLsp X
  have hLY : Submodule.span K (LY : Set V) = Y := cut_span L hLsp Y
  have fgLX : LX.FG := fg_cut L hL X
  have fgLY : LY.FG := fg_cut L hL Y
  set LP := latPow (Fin n) LX with hLPd
  have fgLP : LP.FG := Submodule.fg_pi fun _ => fgLX
  have hLPsp : Submodule.span K (LP : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hLPd, span_latPow, hLX]
  have hLPX : ∀ x ∈ LP, x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun x hx i _ =>
    (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  set A := LP.map ((Φt Φ).restrictScalars (𝓞 K)) with hAd
  have fgA : A.FG := fgLP.map _
  have hAle : A ≤ LY := by
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, H.phi_mem x (hLPX x hx)⟩
    simp only [LinearMap.coe_restrictScalars, Φt_apply]
    exact L.sum_mem fun i _ => hΦL i (x i) (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).1
      (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  have hAsp : Submodule.span K (A : Set V) = Y := by
    rw [hAd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLPsp, H.map_phi]
  refine ⟨hAle, hAsp, idx_nonneg_of_le hI w LY A fgLY fgA (hLY.trans hAsp.symm) hAle, ?_⟩

  set Bt := LY.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) with hBtd
  have fgBt : Bt.FG := fgLY.map _
  have hBle : Bt ≤ LP := by
    rintro _ ⟨y, hy, rfl⟩ j _
    have hy' := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨hΨL j y hy'.1 hy'.2, H.h3 j y hy'.2⟩
  have hBsp : Submodule.span K (Bt : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hBtd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLY, H.map_psi]
  have hΨA : A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) = LP.map ((matV Γ).restrictScalars (𝓞 K)) := by
    rw [hAd, ← Submodule.map_comp]
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (H.psiPhi x (hLPX x hx)).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, H.psiPhi x (hLPX x hx)⟩
  have hmat := idx_matV hI w LX fgLX Γ H.det
  rw [← hLPd, ← hΨA] at hmat
  have hΨAsp : Submodule.span K ((A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → V)) :
      Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hΨA]; exact span_map_matV Γ H.det LP X hLPsp
  have hch := idx_chain hI w LP Bt (A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K))) fgLP fgBt (fgA.map _)
    (by rw [hLPsp, hBsp]) (by rw [hΨAsp, hBsp])
  have hinj := idx_map_inj hI w (LinearMap.pi Ψ) LY A fgLY fgA (hLY.trans hAsp.symm)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp hy).2 h0)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp (hAle hy)).2 h0)
  have hnn := idx_nonneg_of_le hI w LP Bt fgLP fgBt (by rw [hLPsp, hBsp]) hBle
  rw [← hBtd] at hinj
  rw [hmat, ← hinj] at hch
  linarith

end Side


end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv


end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW


end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open PI.Dv

section Theta

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)

def theta (M : Module.End K (T.W s)) : MonoidAlgebra K G :=
  ∑ y : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s y⁻¹ * M)) • MonoidAlgebra.of K G y

theorem theta_one : theta T s 1 = eS T s := by simp [theta, eS]

theorem theta_add (M N : Module.End K (T.W s)) : theta T s (M + N) = theta T s M + theta T s N := by
  simp [theta, mul_add, add_smul, Finset.sum_add_distrib]

theorem theta_smul (c : K) (M : Module.End K (T.W s)) : theta T s (c • M) = c • theta T s M := by
  simp only [theta, Finset.smul_sum, smul_smul, mul_smul_comm, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring_nf

theorem theta_zero : theta T s 0 = 0 := by simp [theta]

theorem theta_eq' (M : Module.End K (T.W s)) : theta T s M =
    ∑ y : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (M * T.tau s y⁻¹)) • MonoidAlgebra.of K G y := by
  simp only [theta, LinearMap.trace_mul_comm K (T.tau s _) M]

theorem mul_eS (z : MonoidAlgebra K G) : z * eS T s = theta T s ((T.tau s).asAlgebraHom z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp [theta_zero]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, theta_add]
  | single g r =>
    rw [Representation.asAlgebraHom_single, theta_smul, eS, Finset.mul_sum, theta, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => ?_)
    simp only [Equiv.coe_mulLeft, mul_smul_comm, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
      mul_one, smul_smul]
    rw [← map_mul, mul_inv_rev, inv_mul_cancel_right, MonoidAlgebra.smul_single', MonoidAlgebra.smul_single', mul_one]
    congr 1
    ring

theorem eS_mul (z : MonoidAlgebra K G) : eS T s * z = theta T s ((T.tau s).asAlgebraHom z) := by
  rw [theta_eq']
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, hx, hy, map_add]
    simp only [add_mul, map_add, mul_add, add_smul, Finset.sum_add_distrib]
  | single g r =>
    rw [Representation.asAlgebraHom_single, eS, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => ?_)
    simp only [Equiv.coe_mulRight, smul_mul_assoc, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
      one_mul, smul_smul, smul_mul_assoc, mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    rw [← map_mul, mul_inv_rev, mul_inv_cancel_left, MonoidAlgebra.smul_single', MonoidAlgebra.smul_single', mul_one]
    congr 1
    ring

theorem eS_central (z : MonoidAlgebra K G) : eS T s * z = z * eS T s := by
  rw [eS_mul, mul_eS]

theorem mul_eS_eq (z z' : MonoidAlgebra K G)
    (hz : (T.tau s).asAlgebraHom z = (T.tau s).asAlgebraHom z') : z * eS T s = z' * eS T s := by
  rw [mul_eS, mul_eS, hz]

theorem tau_central_scalar (c : MonoidAlgebra K G) (hc : ∀ z, c * z = z * c) :
    ∃ μ : K, (T.tau s).asAlgebraHom c = μ • 1 := by
  have hmem : (T.tau s).asAlgebraHom c ∈ Subalgebra.center K (Module.End K (T.W s)) := by
    rw [Subalgebra.mem_center_iff]
    intro M
    obtain ⟨z, rfl⟩ := T.irr s M
    rw [← map_mul, ← map_mul, hc z]
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hmem
  obtain ⟨μ, hμ⟩ := hmem
  exact ⟨μ, by rw [← hμ, Algebra.algebraMap_eq_smul_one]⟩

theorem tau_eS [CharZero K] : (T.tau s).asAlgebraHom (eS T s) = 1 := by
  obtain ⟨μ, hμ⟩ := tau_central_scalar T s (eS T s) (eS_central T s)
  set d := Module.finrank K (T.W s) with hd
  have hd0 : (d : K) ≠ 0 := by
    have : 0 < d := Module.finrank_pos
    exact_mod_cast this.ne'
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

  set Ξ : Module.End K (Module.End K (T.W s)) := ∑ y : G,
    (((d : K) / ((Fintype.card G : ℕ) : K)) •
      ((LinearMap.trace K (T.W s)) ∘ₗ LinearMap.mulLeft K (T.tau s y⁻¹))).smulRight (T.tau s y) with hΞ
  have hΞapp : ∀ M, Ξ M = (T.tau s).asAlgebraHom (theta T s M) := by
    intro M
    rw [hΞ, theta, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, Representation.asAlgebraHom_of, LinearMap.smulRight_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_eq_mul]
  have hΞμ : Ξ = μ • LinearMap.id := by
    apply LinearMap.ext; intro M
    obtain ⟨z, rfl⟩ := T.irr s M
    rw [hΞapp, ← mul_eS, map_mul, hμ]
    simp
  have htr := congrArg (LinearMap.trace K _) hΞμ
  rw [hΞ, map_sum, map_smul, LinearMap.trace_id, Module.finrank_linearMap] at htr
  simp only [LinearMap.trace_smulRight, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ← map_mul, inv_mul_cancel, map_one, LinearMap.trace_one, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at htr
  have : μ = 1 := by
    rw [← hd] at htr
    push_cast at htr
    field_simp at htr
    first
    | exact htr.symm
    | exact htr
    | (have h2 : (d : K) * d ≠ 0 := mul_ne_zero hd0 hd0
       apply mul_right_cancel₀ h2
       linear_combination -htr)
  rw [hμ, this, one_smul]

theorem eS_idem [CharZero K] : eS T s * eS T s = eS T s := by
  rw [mul_eS, tau_eS, theta_one]

end Theta

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open Matrix

theorem root_pow_eq_one {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hM : M ^ m = 1)
    (μ : ℂ) (hμ : μ ∈ M.charpoly.roots) : μ ^ m = 1 := by
  have hroot : M.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hMv : M *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, funext_iff, Pi.smul_apply, smul_eq_mul]
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have := hpow m
  rw [hM, Matrix.one_mulVec] at this
  have h2 : (μ ^ m - 1) • v = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv0

theorem trace_finite_order {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hm : 0 < m)
    (hM : M ^ m = 1) : ‖M.trace‖ ≤ Fintype.card d ∧ IsIntegral ℤ M.trace := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  have hroots : ∀ μ ∈ M.charpoly.roots, μ ^ m = 1 := root_pow_eq_one M m hM
  constructor
  · calc ‖M.charpoly.roots.sum‖ ≤ (M.charpoly.roots.map norm).sum := norm_multiset_sum_le _
      _ = (M.charpoly.roots.map (fun _ => (1 : ℝ))).sum := by
          congr 1
          exact Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'
      _ = Multiset.card M.charpoly.roots := by simp
      _ ≤ M.charpoly.natDegree := by exact_mod_cast Polynomial.card_roots' _
      _ = Fintype.card d := by rw [Matrix.charpoly_natDegree_eq_dim]
  · have : ∀ μ ∈ M.charpoly.roots, μ ∈ integralClosure ℤ ℂ := fun μ hμ =>
      IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)
    exact Subalgebra.multiset_sum_mem _ this

theorem trace_end_finite_order {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ Module.finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by
  set b := Module.finBasis K W
  set A := LinearMap.toMatrixAlgEquiv b f with hA
  have htr : LinearMap.trace K W f = A.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b f, hA]; rfl
  have hAm : A ^ m = 1 := by rw [hA, ← map_pow, hf, map_one]
  set B := σ.mapMatrix A with hB
  have hBm : B ^ m = 1 := by rw [hB, ← map_pow, hAm, map_one]
  have hσtr : σ (A.trace) = B.trace := by
    simp [Matrix.trace, hB, map_sum]
  obtain ⟨h1, h2⟩ := trace_finite_order B m hm hBm
  rw [htr, hσtr]
  refine ⟨by simpa using h1, ?_⟩
  rw [← hσtr] at h2
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp h2

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section Orth

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G)

theorem coeff_sum_of (a : G → K) (g : G) :
    (∑ y : G, a y • MonoidAlgebra.of K G y).coeff g = a g := by
  classical
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single_apply, Finsupp.single_apply]

theorem eS_ne_zero (s : T.S) : eS T s ≠ 0 := by
  intro h
  have := tau_eS T s
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem eS_orth (s t : T.S) (hst : s ≠ t) : eS T s * eS T t = 0 := by
  obtain ⟨μ, hμ⟩ := tau_central_scalar T t (eS T s) (fun z => eS_central T s z)
  obtain ⟨ν, hν⟩ := tau_central_scalar T s (eS T t) (fun z => eS_central T t z)
  have h1 : eS T s * eS T t = μ • eS T t := by rw [mul_eS T t, hμ, theta_smul, theta_one]
  have h2 : eS T s * eS T t = ν • eS T s := by
    rw [← eS_central T t (eS T s), mul_eS T s, hν, theta_smul, theta_one]
  by_contra hne
  have hμ0 : μ ≠ 0 := fun h => hne (by rw [h1, h, zero_smul])
  have h3 : eS T t = (μ⁻¹ * ν) • eS T s := by
    rw [mul_smul, ← h2, h1, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  set κ := μ⁻¹ * ν with hκ
  have hsne := eS_ne_zero T s
  have htne := eS_ne_zero T t
  have h4 : κ = 1 := by
    have e1 : eS T t = (κ * κ) • eS T s := by
      conv_lhs => rw [← eS_idem T t, h3]
      rw [smul_mul_smul_comm, eS_idem]
    have e2 : (κ * κ - κ) • eS T s = 0 := by rw [sub_smul, ← e1, ← h3, sub_self]
    rcases smul_eq_zero.mp e2 with h | h
    · have hκ0 : κ ≠ 0 := fun h0 => htne (by rw [h3, h0, zero_smul])
      have : κ * (κ - 1) = 0 := by rw [mul_sub, mul_one]; exact h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hκ0
      · exact sub_eq_zero.mp h'
    · exact absurd h hsne
  have h5 : eS T t = eS T s := by rw [h3, h4, one_smul]
  have hc : ∀ g : G, (((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W t) (T.tau t g⁻¹)) = (((Module.finrank K (T.W s) : ℕ) : K) /
      ((Fintype.card G : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s g⁻¹)) := by
    intro g
    have := congrArg (fun z : MonoidAlgebra K G => z.coeff g) h5
    simp only [eS] at this
    rwa [coeff_sum_of, coeff_sum_of] at this
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : Module.finrank K (T.W t) = Module.finrank K (T.W s) := by
    have := hc 1
    simp only [inv_one, map_one, LinearMap.trace_one] at this
    field_simp at this
    have h' : ((Module.finrank K (T.W t) ^ 2 : ℕ) : K) = ((Module.finrank K (T.W s) ^ 2 : ℕ) : K) := by
      push_cast; linear_combination this
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) (by exact_mod_cast h')
  have hdK : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0 := by
    have : 0 < Module.finrank K (T.W s) := Module.finrank_pos
    exact_mod_cast this.ne'
  apply hst
  apply T.inj
  funext g
  have := hc g⁻¹
  rw [hd, inv_inv] at this
  have hne0 : ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0 := div_ne_zero hdK hG0
  exact (mul_left_cancel₀ hne0 this).symm


end Orth

section Eps

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

open Classical in

def chiT (P : Pair K G) (x : G) : K := if h : x ∈ P.H then (((P.chi ⟨x, h⟩)⁻¹ : Kˣ) : K) else 0

def epsS (P : Pair K G) : MonoidAlgebra K G := ∑ x : G, chiT P x • MonoidAlgebra.of K G x

theorem eps_eq (P : Pair K G) : eps P = ((Nat.card P.H : ℕ) : K)⁻¹ • epsS P := by
  classical
  rw [eps, epsS]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ P.H
  · simp only [chiT, dif_pos hx]
  · simp only [chiT, dif_neg hx, zero_smul]

theorem chiT_mul (P : Pair K G) (h : P.H) (x : G) :
    chiT P x = ((P.chi h : Kˣ) : K) * chiT P ((h : G) * x) := by
  classical
  by_cases hx : x ∈ P.H
  · have hhx : (h : G) * x ∈ P.H := P.H.mul_mem h.2 hx
    simp only [chiT, dif_pos hx, dif_pos hhx]
    have : (⟨(h : G) * x, hhx⟩ : P.H) = h * ⟨x, hx⟩ := rfl
    rw [this, map_mul, mul_inv_rev, Units.val_mul, ← mul_assoc, mul_right_comm, Units.mul_inv, one_mul]
  · have hhx : (h : G) * x ∉ P.H := fun hh => hx (by simpa using P.H.mul_mem (P.H.inv_mem h.2) hh)
    simp only [chiT, dif_neg hx, dif_neg hhx, mul_zero]

theorem chiT_of_mem (P : Pair K G) (x : G) (hx : x ∈ P.H) :
    chiT P x = (((P.chi ⟨x, hx⟩)⁻¹ : Kˣ) : K) := by
  classical
  simp only [chiT, dif_pos hx]

theorem chiT_of_not_mem (P : Pair K G) (x : G) (hx : x ∉ P.H) : chiT P x = 0 := by
  classical
  simp only [chiT, dif_neg hx]

theorem of_mul_epsS (P : Pair K G) (h : P.H) :
    MonoidAlgebra.of K G (h : G) * epsS P = ((P.chi h : Kˣ) : K) • epsS P := by
  rw [epsS, Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (h : G)) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [mul_smul_comm, ← map_mul, smul_smul, ← chiT_mul]

theorem card_H_pos (P : Pair K G) : 0 < Nat.card P.H := Nat.card_pos

theorem epsS_mul_epsS (P : Pair K G) : epsS P * epsS P = ((Nat.card P.H : ℕ) : K) • epsS P := by
  classical
  nth_rewrite 1 [epsS]
  rw [Finset.sum_mul]
  have : ∀ x : G, (chiT P x • MonoidAlgebra.of K G x) * epsS P = (if x ∈ P.H then (1 : K) else 0) • epsS P := by
    intro x
    by_cases hx : x ∈ P.H
    · rw [if_pos hx, smul_mul_assoc, of_mul_epsS P ⟨x, hx⟩, smul_smul, chiT_of_mem P x hx,
        Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
    · rw [if_neg hx, chiT_of_not_mem P x hx, zero_smul, zero_mul, zero_smul]
  rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_smul, Finset.sum_boole]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem eps_idem (P : Pair K G) : eps P * eps P = eps P := by
  rw [eps_eq, smul_mul_smul_comm, epsS_mul_epsS, smul_smul]
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  congr 1
  field_simp

theorem eps_mul_epsS (P : Pair K G) : eps P * epsS P = epsS P := by
  rw [eps_eq, smul_mul_assoc, epsS_mul_epsS, smul_smul]
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  rw [inv_mul_cancel₀ this, one_smul]

end Eps

section RankOne

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem rank_one_sandwich (p : Module.End K W) (hp : p * p = p) (h1 : Module.finrank K (LinearMap.range p) = 1)
    (X : Module.End K W) : p * X * p = LinearMap.trace K W (p * X) • p := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨β, hβ⟩ := hv ⟨p (X v), LinearMap.mem_range_self p _⟩
  have hβ' : p (X v) = β • (v : W) := by
    have := congrArg Subtype.val hβ; simpa using this.symm
  have key : p * X * p = β • p := by
    apply LinearMap.ext; intro w
    obtain ⟨c, hc⟩ := hv ⟨p w, LinearMap.mem_range_self p w⟩
    have hc' : p w = c • (v : W) := by have := congrArg Subtype.val hc; simpa using this.symm
    simp only [Module.End.mul_apply, LinearMap.smul_apply]
    rw [hc', map_smul, map_smul, hβ', smul_comm]
  have htp : LinearMap.trace K W p = 1 := by
    rw [(LinearMap.IsIdempotentElem.isProj_range p hp).trace, h1, Nat.cast_one]
  have htr : LinearMap.trace K W (p * X) = β := by
    have : LinearMap.trace K W (p * X * p) = LinearMap.trace K W (p * X) := by
      rw [LinearMap.trace_mul_comm, ← mul_assoc, hp]
    rw [← this, key, map_smul, htp, smul_eq_mul, mul_one]
  rw [htr, key]

end RankOne

section Integral

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

def ιO : MonoidAlgebra (𝓞 K) G →ₐ[𝓞 K] MonoidAlgebra K G :=
  MonoidAlgebra.mapAlgHom G (Algebra.ofId (𝓞 K) K)

def IntR (z : MonoidAlgebra K G) : Prop := z ∈ (ιO (K := K) (G := G)).range

theorem intEl_of_intR (z : MonoidAlgebra K G) (hz : IntR z) : IntEl z := by
  obtain ⟨w, rfl⟩ := hz
  intro g
  exact ⟨w.coeff g, by simp [ιO]⟩

theorem intR_of (g : G) : IntR (MonoidAlgebra.of K G g) :=
  ⟨MonoidAlgebra.of (𝓞 K) G g, by simp [ιO, MonoidAlgebra.of_apply]⟩

theorem intR_mul {z z' : MonoidAlgebra K G} (hz : IntR z) (hz' : IntR z') : IntR (z * z') :=
  Subalgebra.mul_mem _ hz hz'

theorem intR_zero : IntR (0 : MonoidAlgebra K G) := Subalgebra.zero_mem _

theorem intR_sum {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra K G) (hf : ∀ i ∈ s, IntR (f i)) :
    IntR (∑ i ∈ s, f i) := Subalgebra.sum_mem _ hf

theorem intR_smul (c : K) (hc : c ∈ Set.range (algebraMap (𝓞 K) K)) {z : MonoidAlgebra K G} (hz : IntR z) :
    IntR (c • z) := by
  obtain ⟨u, rfl⟩ := hc
  rw [algebraMap_smul]
  exact Subalgebra.smul_mem _ hz u

theorem mem_O_of_isIntegral (x : K) (hx : IsIntegral ℤ x) : x ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨IsIntegralClosure.mk' (𝓞 K) x hx, IsIntegralClosure.algebraMap_mk' _ _ _⟩

theorem mem_O_of_pow (x : K) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : x ∈ Set.range (algebraMap (𝓞 K) K) :=
  mem_O_of_isIntegral x (IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one))

theorem exists_embedding : Nonempty (K →+* ℂ) := by
  rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
  exact Module.finrank_pos

theorem chi_inv_pow (P : Pair K G) (h : P.H) : ((((P.chi h)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by
  classical
  rw [← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, Nat.card_eq_fintype_card, pow_card_eq_one, map_one,
    inv_one, Units.val_one]

theorem intR_epsS (P : Pair K G) : IntR (epsS P) := by
  refine intR_sum _ _ fun x _ => ?_
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    exact intR_smul _ (mem_O_of_pow _ _ (card_H_pos P) (chi_inv_pow P ⟨x, hx⟩)) (intR_of x)
  · rw [chiT_of_not_mem P x hx, zero_smul]; exact intR_zero

theorem trace_tau_mem {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (g : G) : LinearMap.trace K W (τ g) ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨σ⟩ := exists_embedding (K := K)
  have h := (trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2
  exact mem_O_of_isIntegral _ h

theorem norm_trace_tau_le {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W (τ g))‖ ≤ Module.finrank K W :=
  (trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1


end Integral

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

section Span

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem exists_dual_one (w : W) (hw : w ≠ 0) : ∃ φ : Module.Dual K W, φ w = 1 := by
  by_contra h
  push_neg at h
  apply hw
  rw [← Module.forall_dual_apply_eq_zero_iff K w]
  intro φ
  by_contra hφ
  exact h ((φ w)⁻¹ • φ) (by simp [inv_mul_cancel₀ hφ])

theorem asAlgebraHom_mem_span (τ : Representation K G W) (z : MonoidAlgebra K G) (w : W) :
    τ.asAlgebraHom z w ∈ Submodule.span K (Set.range fun x => τ x w) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | single x r =>
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

theorem exists_end_map (w u : W) (hw : w ≠ 0) : ∃ M : Module.End K W, M w = u := by
  obtain ⟨φ, hφ⟩ := exists_dual_one (K := K) w hw
  exact ⟨φ.smulRight u, by rw [LinearMap.smulRight_apply, hφ, one_smul]⟩

theorem span_orbit (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom) (w : W) (hw : w ≠ 0) :
    Submodule.span K (Set.range fun x => τ x w) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨M, hM⟩ := exists_end_map (K := K) w u hw
  obtain ⟨z, hz⟩ := hirr M
  have := asAlgebraHom_mem_span τ z w
  rwa [hz, hM] at this

theorem finrank_le_card (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom)
    [Nontrivial W] : Module.finrank K W ≤ Fintype.card G := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  rw [← finrank_top, ← span_orbit τ hirr w hw]
  exact finrank_range_le_card _

end Span

section Select

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem select_li {ι : Type} (F : ι → V) (hF : Submodule.span K (Set.range F) = ⊤) :
    ∃ g : Fin (Module.finrank K V) → ι, LinearIndependent K (F ∘ g) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K F
  rw [hF] at hsp
  let b := Module.Basis.mk hli (by rw [hsp])
  letI := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card κ = Module.finrank K V := (Module.finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨a ∘ e.symm, ?_⟩
  have := hli.comp e.symm e.symm.injective
  simpa [Function.comp_assoc] using this

theorem li_span_top {n : ℕ} (u : Fin n → V) (hu : LinearIndependent K u) (hn : n = Module.finrank K V) :
    Submodule.span K (Set.range u) = ⊤ := by
  have h := linearIndependent_iff_card_eq_finrank_span.mp hu
  apply Submodule.eq_top_of_finrank_eq
  show Set.finrank K (Set.range u) = _
  rw [← h, Fintype.card_fin, hn]

theorem dual_span {ι : Type} (ψ : ι → Module.Dual K V) (h : ∀ v, (∀ i, ψ i v = 0) → v = 0) :
    Submodule.span K (Set.range ψ) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := (Submodule.span K (Set.range ψ)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  set v := (Module.evalEquiv K V).symm f with hvd
  have hv : ∀ φ : Module.Dual K V, f φ = φ v := by
    intro φ
    have : Module.evalEquiv K V v = f := by rw [hvd, LinearEquiv.apply_symm_apply]
    rw [← this]
    rfl
  have hv0 : v = 0 := h v (fun i => by rw [← hv]; exact hle (Submodule.subset_span ⟨i, rfl⟩))
  apply hf0
  ext φ
  rw [hv, hv0, map_zero]
  rfl

end Select

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section H

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W)

theorem epsS_eq_smul (P : Pair K G) : epsS P = ((Nat.card P.H : ℕ) : K) • eps P := by
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  rw [eps_eq, smul_smul, mul_inv_cancel₀ this, one_smul]

theorem tau_eps_idem (P : Pair K G) : τ.asAlgebraHom (eps P) * τ.asAlgebraHom (eps P) = τ.asAlgebraHom (eps P) := by
  rw [← map_mul, eps_idem]

theorem trace_mem_of_intR (z : MonoidAlgebra K G) (hz : IntR z) :
    LinearMap.trace K W (τ.asAlgebraHom z) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hz' := intEl_of_intR z hz
  have key : LinearMap.trace K W (τ.asAlgebraHom z) ∈ (algebraMap (𝓞 K) K).range := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, map_sum]
    refine Subring.sum_mem _ fun g _ => ?_
    rw [map_smul, smul_eq_mul]
    exact Subring.mul_mem _ (RingHom.mem_range.mpr (hz' g)) (RingHom.mem_range.mpr (trace_tau_mem τ g))
  exact RingHom.mem_range.mp key

theorem sandwich (P0 : Pair K G) (h1 : Module.finrank K (LinearMap.range (τ.asAlgebraHom (eps P0))) = 1)
    (z : MonoidAlgebra K G) :
    τ.asAlgebraHom (epsS P0 * z * eps P0) =
      LinearMap.trace K W (τ.asAlgebraHom (epsS P0 * z)) • τ.asAlgebraHom (eps P0) := by
  have hL : τ.asAlgebraHom (epsS P0 * z * eps P0) = ((Nat.card P0.H : ℕ) : K) •
      (τ.asAlgebraHom (eps P0) * τ.asAlgebraHom z * τ.asAlgebraHom (eps P0)) := by
    rw [epsS_eq_smul, smul_mul_assoc, smul_mul_assoc, map_smul, map_mul, map_mul]
  have hR : LinearMap.trace K W (τ.asAlgebraHom (epsS P0 * z)) = ((Nat.card P0.H : ℕ) : K) *
      LinearMap.trace K W (τ.asAlgebraHom (eps P0) * τ.asAlgebraHom z) := by
    rw [epsS_eq_smul, smul_mul_assoc, map_smul, map_smul, map_mul, smul_eq_mul]
  rw [hL, hR, rank_one_sandwich _ (tau_eps_idem τ P0) h1, smul_smul]

end H

section Absorb

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem absorb_eps (T : GoodSet K G) (s : T.S) (Q R : Pair K G) (z : MonoidAlgebra K G) :
    eps Q * eS T s * (epsS Q * z) * (eps R * eS T s) = epsS Q * z * (eps R * eS T s) := by
  calc eps Q * eS T s * (epsS Q * z) * (eps R * eS T s)
      = eps Q * (eS T s * (epsS Q * z * eps R)) * eS T s := by simp only [mul_assoc]
    _ = eps Q * ((epsS Q * z * eps R) * eS T s) * eS T s := by rw [eS_central]
    _ = (eps Q * epsS Q) * z * eps R * (eS T s * eS T s) := by simp only [mul_assoc]
    _ = epsS Q * z * (eps R * eS T s) := by rw [eps_mul_epsS, eS_idem]; simp only [mul_assoc]

end Absorb

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section PerS

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem perS (T : GoodSet K G) (P0 P : Pair K G) (hM1 : M1 T P0) (s : T.S) :
    ∃ (g g' : Fin (nS T P s) → G) (Γ : Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)),
      (∀ j k, algebraMap (𝓞 K) K (Γ j k) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k))))) ∧
      Γ.det ≠ 0 ∧
      ∃ b' : Fin (nS T P s) → MonoidAlgebra K G,
        (∀ i, b' i * (eps P * eS T s) = eps P0 * eS T s * b' i * (eps P * eS T s)) ∧
        ∑ i, (epsS P * MonoidAlgebra.of K G (g i)) * b' i * (eps P * eS T s) = eps P * eS T s := by
  classical
  set τ := T.tau s with hτ
  set p := τ.asAlgebraHom (eps P) with hp_def
  set p0 := τ.asAlgebraHom (eps P0) with hp0_def
  have hp : p * p = p := tau_eps_idem τ P
  have hp0 : p0 * p0 = p0 := tau_eps_idem τ P0
  have h1 : Module.finrank K (LinearMap.range p0) = 1 := hM1 s
  set n := nS T P s with hn_def
  have hn : Module.finrank K (LinearMap.range p) = n := by rw [hn_def]; rfl
  clear_value n

  obtain ⟨v0', hv0ne, hv0⟩ := finrank_eq_one_iff'.mp h1
  set v0 : T.W s := v0'.1 with hv0_def
  have hv0ne' : v0 ≠ 0 := fun h => hv0ne (Subtype.ext h)
  have hpv0 : p0 v0 = v0 := by
    obtain ⟨w, hw⟩ := v0'.2
    rw [hv0_def, ← hw, ← Module.End.mul_apply, hp0]
  obtain ⟨f0, hf0⟩ := exists_dual_one (K := K) v0 hv0ne'
  have hline : ∀ w, p0 w = f0 (p0 w) • v0 := by
    intro w
    obtain ⟨c, hc⟩ := hv0 ⟨p0 w, LinearMap.mem_range_self _ _⟩
    have hc' : c • v0 = p0 w := congrArg Subtype.val hc
    rw [← hc', map_smul, hf0, smul_eq_mul, mul_one]

  let pc : T.W s →ₗ[K] LinearMap.range p := LinearMap.codRestrict _ p (fun w => LinearMap.mem_range_self p w)
  let F : G → LinearMap.range p := fun x => pc (τ x v0)
  have hF : Submodule.span K (Set.range F) = ⊤ := by
    have : Set.range F = pc '' Set.range (fun x => τ x v0) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, span_orbit τ (T.irr s) v0 hv0ne', Submodule.map_top, LinearMap.range_eq_top]
    rintro ⟨u, w, rfl⟩
    exact ⟨w, rfl⟩
  obtain ⟨g0, hg0⟩ := select_li F hF
  let g : Fin n → G := g0 ∘ Fin.cast hn.symm
  have hg : LinearIndependent K (F ∘ g) := hg0.comp _ (Fin.cast_injective _)

  let ψ : G → Module.Dual K (LinearMap.range p) := fun x =>
    (f0 ∘ₗ p0 ∘ₗ τ x) ∘ₗ (LinearMap.range p).subtype
  have hψapp : ∀ x (u : LinearMap.range p), ψ x u = f0 (p0 (τ x u)) := fun x u => rfl
  have hψ : ∀ u : LinearMap.range p, (∀ x, ψ x u = 0) → u = 0 := by
    intro u hu
    by_contra hne
    have hne' : (u : T.W s) ≠ 0 := fun h => hne (Subtype.ext h)
    have hall : ∀ w, f0 (p0 w) = 0 := by
      intro w
      have hw : w ∈ Submodule.span K (Set.range fun x => τ x u) := by
        rw [span_orbit τ (T.irr s) u hne']; trivial
      induction hw using Submodule.span_induction with
      | mem y hy => obtain ⟨x, rfl⟩ := hy; exact hu x
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, map_smul, hy, smul_zero]
    have := hall v0
    rw [hpv0, hf0] at this
    exact one_ne_zero this
  have hψspan := dual_span ψ hψ
  obtain ⟨g'0, hg'0⟩ := select_li ψ hψspan
  have hdn : Module.finrank K (Module.Dual K (LinearMap.range p)) = n := by
    rw [Subspace.dual_finrank_eq, hn]
  let g' : Fin n → G := g'0 ∘ Fin.cast hdn.symm
  have hg' : LinearIndependent K (ψ ∘ g') := hg'0.comp _ (Fin.cast_injective _)
  have hg'span : Submodule.span K (Set.range (ψ ∘ g')) = ⊤ := li_span_top _ hg' hdn.symm
  have hgspan : Submodule.span K (Set.range (F ∘ g)) = ⊤ := li_span_top _ hg hn.symm

  set cH : K := ((Nat.card P.H : ℕ) : K) with hcH
  set cH0 : K := ((Nat.card P0.H : ℕ) : K) with hcH0
  have hcH_ne : cH ≠ 0 := by rw [hcH]; exact_mod_cast (card_H_pos P).ne'
  have hcH0_ne : cH0 ≠ 0 := by rw [hcH0]; exact_mod_cast (card_H_pos P0).ne'
  have hτepsS : τ.asAlgebraHom (epsS P) = cH • p := by rw [epsS_eq_smul, map_smul]
  have hτepsS0 : τ.asAlgebraHom (epsS P0) = cH0 • p0 := by rw [epsS_eq_smul, map_smul]
  have hmem : ∀ j k, LinearMap.trace K (T.W s) (τ.asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k)))) ∈
        Set.range (algebraMap (𝓞 K) K) := fun j k =>
    trace_mem_of_intR τ _ (intR_mul (intR_mul (intR_epsS P0) (intR_of _)) (intR_mul (intR_epsS P) (intR_of _)))
  choose Γf hΓf using hmem
  let Γ : Matrix (Fin n) (Fin n) (𝓞 K) := Matrix.of Γf
  have hkey : ∀ j k, LinearMap.trace K (T.W s) (τ.asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k)))) =
        cH0 * cH * ψ (g' j) (F (g k)) := by
    intro j k
    set X := τ (g' j) * p * τ (g k) with hX
    have e1 : τ.asAlgebraHom (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k))) =
        (cH0 * cH) • (p0 * X) := by
      rw [map_mul, map_mul, map_mul, hτepsS, hτepsS0, Representation.asAlgebraHom_of,
        Representation.asAlgebraHom_of, hX]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      rw [mul_comm cH cH0]
    have e2 : LinearMap.trace K (T.W s) (p0 * X) = f0 (p0 (X v0)) := by
      have hs := rank_one_sandwich p0 hp0 h1 X
      have := congrArg (fun M : Module.End K (T.W s) => f0 (M v0)) hs
      simp only [Module.End.mul_apply, LinearMap.smul_apply, hpv0, map_smul, hf0, smul_eq_mul, mul_one] at this
      exact this.symm
    rw [e1, map_smul, e2, smul_eq_mul, hψapp]
    rfl
  let A : Matrix (Fin n) (Fin n) K := Matrix.of fun j k => ψ (g' j) (F (g k))
  have hΓK : Γ.map (algebraMap (𝓞 K) K) = (cH0 * cH) • A := by
    ext j k
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, A]
    show algebraMap (𝓞 K) K (Γf j k) = _
    exact (hΓf j k).trans (hkey j k)
  have hAdet : A.det ≠ 0 := by
    intro hA
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
    set w : LinearMap.range p := ∑ k, c k • F (g k) with hw
    have hψw : ∀ j, ψ (g' j) w = 0 := by
      intro j
      have := congrFun hc j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, A, Pi.zero_apply] at this
      rw [hw, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hall : ∀ φ : Module.Dual K (LinearMap.range p), φ w = 0 := by
      intro φ
      have hφ : φ ∈ Submodule.span K (Set.range (ψ ∘ g')) := by rw [hg'span]; trivial
      induction hφ using Submodule.span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hψw j
      | zero => rfl
      | add y z _ _ hy hz => rw [LinearMap.add_apply, hy, hz, add_zero]
      | smul a y _ hy => rw [LinearMap.smul_apply, hy, smul_zero]
    have hw0 : w = 0 := (Module.forall_dual_apply_eq_zero_iff K w).mp hall
    have := Fintype.linearIndependent_iff.mp hg c (by rw [← hw0, hw]; rfl)
    exact hc0 (funext this)
  have hdetK : (Γ.map (algebraMap (𝓞 K) K)).det ≠ 0 := by
    rw [hΓK, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hcH0_ne hcH_ne)) hAdet
  have hdetΓ : Γ.det ≠ 0 := by
    intro h
    apply hdetK
    rw [show Γ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K).mapMatrix Γ from rfl, ← RingHom.map_det, h,
      map_zero]
  refine ⟨g, g', Γ, fun j k => hΓf j k, hdetΓ, ?_⟩

  set ΓK := Γ.map (algebraMap (𝓞 K) K) with hΓKd
  set δ := ΓK.det with hδ
  let b : Fin n → MonoidAlgebra K G := fun j => epsS P0 * MonoidAlgebra.of K G (g' j)
  let a : Fin n → MonoidAlgebra K G := fun k => epsS P * MonoidAlgebra.of K G (g k)
  let b' : Fin n → MonoidAlgebra K G := fun i => δ⁻¹ • ∑ j, ΓK.adjugate i j • b j
  have hbY : ∀ j, b j * (eps P * eS T s) = eps P0 * eS T s * b j * (eps P * eS T s) := by
    intro j
    have := absorb_eps T s P0 P (MonoidAlgebra.of K G (g' j))
    exact this.symm
  refine ⟨b', fun i => ?_, ?_⟩
  · simp only [b', smul_mul_assoc, Finset.sum_mul, mul_smul_comm, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hbY j]
  ·
    have hδ0 : δ ≠ 0 := hdetK
    have hbu : ∀ j k, τ.asAlgebraHom (b j) (F (g k) : T.W s) = (ΓK j k * cH⁻¹) • v0 := by
      intro j k
      have hΓ : ΓK j k = cH0 * cH * ψ (g' j) (F (g k)) := (hΓf j k).trans (hkey j k)
      have hb : τ.asAlgebraHom (b j) = cH0 • (p0 * τ (g' j)) := by
        simp only [b, map_mul, hτepsS0, Representation.asAlgebraHom_of, smul_mul_assoc]
      rw [hb, LinearMap.smul_apply, Module.End.mul_apply, hline (τ (g' j) _), smul_smul, hΓ]
      congr 1
      rw [hψapp]
      field_simp
    have hb'u : ∀ i k, τ.asAlgebraHom (b' i) (F (g k) : T.W s) =
        (cH⁻¹ * (1 : Matrix (Fin n) (Fin n) K) i k) • v0 := by
      intro i k
      simp only [b', map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, hbu, smul_smul,
        ← Finset.sum_smul]
      congr 1
      have hadj : ∑ j, ΓK.adjugate i j * ΓK j k = δ * (1 : Matrix (Fin n) (Fin n) K) i k := by
        have := congrFun (congrFun (Matrix.adjugate_mul ΓK) i) k
        rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
        exact this
      have : ∑ j, ΓK.adjugate i j * (ΓK j k * cH⁻¹) = (∑ j, ΓK.adjugate i j * ΓK j k) * cH⁻¹ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hadj]
      field_simp
    set Z' : Module.End K (T.W s) := ∑ i, τ.asAlgebraHom (a i) * τ.asAlgebraHom (b' i) with hZ'
    have hZk : ∀ k, Z' (F (g k) : T.W s) = (F (g k) : T.W s) := by
      intro k
      rw [hZ', LinearMap.sum_apply]
      simp only [Module.End.mul_apply, hb'u, map_smul]
      rw [Finset.sum_eq_single k (fun x _ hx => by rw [Matrix.one_apply_ne hx, mul_zero, zero_smul])
        (by simp), Matrix.one_apply_eq, mul_one]
      have ha : τ.asAlgebraHom (a k) = cH • (p * τ (g k)) := by
        simp only [a, map_mul, hτepsS, Representation.asAlgebraHom_of, smul_mul_assoc]
      rw [ha, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hcH_ne, one_smul, Module.End.mul_apply]
      rfl
    have hrange : ∀ u ∈ LinearMap.range p, u ∈ Submodule.span K (Set.range fun k => (F (g k) : T.W s)) := by
      intro u hu
      have h2 : (⟨u, hu⟩ : LinearMap.range p) ∈ Submodule.span K (Set.range (F ∘ g)) := by
        rw [hgspan]; trivial
      have h3 := Submodule.mem_map_of_mem (f := (LinearMap.range p).subtype) h2
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact h3
    have hZsp : ∀ u ∈ Submodule.span K (Set.range fun k => (F (g k) : T.W s)), Z' u = u := by
      intro u hsp
      induction hsp using Submodule.span_induction with
      | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hZk k
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | smul c y _ hy => rw [map_smul, hy]
    have hZu : ∀ u ∈ LinearMap.range p, Z' u = u := fun u hu => hZsp u (hrange u hu)
    have hZ : τ.asAlgebraHom (∑ i, a i * b' i * eps P) = p := by
      rw [map_sum]
      simp only [map_mul]
      rw [← Finset.sum_mul, ← hZ']
      apply LinearMap.ext; intro w
      rw [Module.End.mul_apply, hZu _ (LinearMap.mem_range_self p w)]
    calc ∑ i, a i * b' i * (eps P * eS T s) = (∑ i, a i * b' i * eps P) * eS T s := by
          rw [Finset.sum_mul]; simp only [mul_assoc]
      _ = eps P * eS T s := mul_eS_eq T s _ _ (by rw [hZ])

end PerS

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section Bound

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem norm_chiT_le (P : Pair K G) (x : G) (σ : K →+* ℂ) : ‖σ (chiT P x)‖ ≤ 1 := by
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    have h := chi_inv_pow P ⟨x, hx⟩
    have h2 : (σ (((P.chi ⟨x, hx⟩)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by rw [← map_pow, h, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h2 (card_H_pos P).ne').le
  · rw [chiT_of_not_mem P x hx, map_zero, norm_zero]; exact zero_le_one

theorem prod_expand (c c' : G → K) (g' g : G) :
    (∑ x : G, c x • MonoidAlgebra.of K G x) * MonoidAlgebra.of K G g' *
        ((∑ y : G, c' y • MonoidAlgebra.of K G y) * MonoidAlgebra.of K G g) =
      ∑ x : G, ∑ y : G, (c x * c' y) • MonoidAlgebra.of K G (x * g' * (y * g)) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hof : MonoidAlgebra.of K G x * MonoidAlgebra.of K G g' * (MonoidAlgebra.of K G y * MonoidAlgebra.of K G g) =
      MonoidAlgebra.of K G (x * g' * (y * g)) := by simp only [map_mul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hof, mul_comm (c' y) (c x)]

theorem entry_bound (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (g' g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G g' * (epsS P * MonoidAlgebra.of K G g))))‖ ≤
      ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
  have hd : (Module.finrank K (T.W s) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast finrank_le_card (T.tau s) (T.irr s)
  rw [epsS, epsS, prod_expand, map_sum, map_sum, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x y : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      ((chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖ ≤ (Fintype.card G : ℝ) := by
    intro x y
    rw [map_smul, map_smul, Representation.asAlgebraHom_of, smul_eq_mul, map_mul, map_mul, norm_mul, norm_mul]
    have h1 := norm_chiT_le P0 x σ
    have h2 := norm_chiT_le P y σ
    have h3 := norm_trace_tau_le (T.tau s) (x * g' * (y * g)) σ
    calc ‖σ (chiT P0 x)‖ * ‖σ (chiT P y)‖ * ‖σ (LinearMap.trace K (T.W s) ((T.tau s) (x * g' * (y * g))))‖
        ≤ 1 * 1 * (Module.finrank K (T.W s) : ℝ) := by
          gcongr
      _ ≤ _ := by rw [one_mul, one_mul]; exact hd
  calc ∑ x : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (∑ y : G, (chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖
      ≤ ∑ x : G, ∑ y : G, (Fintype.card G : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [map_sum, map_sum, map_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hterm x y)
    _ = ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Bound


end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW


end PI.Dv.TIW
end
end
