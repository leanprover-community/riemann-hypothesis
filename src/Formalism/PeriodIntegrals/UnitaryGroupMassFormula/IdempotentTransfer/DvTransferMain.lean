import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.CharacteristicPolynomialCompatibility
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegTop
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.FinalCor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegGeOfInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.FgOfLeL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.ESMulESOfNeZero

section
noncomputable section

namespace PI.Dv.Tr

open Module

lemma root_pow_eq_one {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (m : ℕ) (hB : B ^ m = 1) (μ : ℂ)
    (hμ : μ ∈ B.charpoly.roots) : μ ^ m = 1 := by
  have hroot : B.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic B).ne_zero).mp hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hsc : Matrix.mulVec (Matrix.scalar n μ) v = μ • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hBv : Matrix.mulVec B v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero, hsc] at hv
    exact hv.symm
  have hpow : ∀ k : ℕ, Matrix.mulVec (B ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h1 := hpow m
  rw [hB, Matrix.one_mulVec] at h1
  by_contra hne
  have h2 : (1 - μ ^ m) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact hne (by linear_combination -h)
  · exact hv0 h

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

lemma trace_finite_order (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by
  classical
  let b := Module.finBasis K W
  set A := LinearMap.toMatrix b b f with hAdef
  set B : Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ := σ.mapMatrix A with hBdef
  have htr : σ (LinearMap.trace K W f) = B.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b, hBdef]
    simp [Matrix.trace, map_sum, RingHom.mapMatrix_apply, hAdef]
  have hApow : ∀ k : ℕ, A ^ k = LinearMap.toMatrix b b (f ^ k) := by
    intro k
    induction k with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, ih, pow_succ, LinearMap.toMatrix_mul]
  have hB : B ^ m = 1 := by
    rw [hBdef, ← map_pow, hApow, hf, LinearMap.toMatrix_one, map_one]
  have hroots : ∀ μ ∈ B.charpoly.roots, μ ^ m = 1 := fun μ hμ => root_pow_eq_one B m hB μ hμ
  have hsum : B.trace = B.charpoly.roots.sum := Matrix.trace_eq_sum_roots_charpoly B
  constructor
  · rw [htr, hsum]
    refine (norm_multiset_sum_le _).trans ?_
    have hmap : B.charpoly.roots.map (fun μ => ‖μ‖) = B.charpoly.roots.map (fun _ => (1 : ℝ)) :=
      Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'
    rw [hmap, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
    have hc := Polynomial.card_roots' B.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hc
    exact_mod_cast hc
  · have hint : IsIntegral ℤ (σ (LinearMap.trace K W f)) := by
      rw [htr, hsum]
      exact IsIntegral.multiset_sum fun μ hμ =>
        IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)
    exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp hint

end PI.Dv.Tr
end
end

section
noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section Alg2

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

lemma eS_mul_eG (T : GoodSet K G) (s : T.S) : eS T s * eG T = eS T s := by
  classical
  rw [eG, Finset.mul_sum, Finset.sum_eq_single s]
  · exact eS_idem T s
  · intro t _ ht; exact eS_orth T s t (Ne.symm ht)
  · simp

lemma eG_mul_eS (T : GoodSet K G) (s : T.S) : eG T * eS T s = eS T s := by
  rw [← eG_comm, eS_mul_eG]

lemma card_S_le (T : GoodSet K G) : Fintype.card T.S ≤ Fintype.card G := by
  classical
  set U := Submodule.span K (Set.range (MonoidAlgebra.of K G)) with hU
  have hmem : ∀ s, eS T s ∈ U := fun s =>
    U.sum_mem fun y _ => U.smul_mem _ (Submodule.subset_span ⟨y, rfl⟩)
  let v : T.S → U := fun s => ⟨eS T s, hmem s⟩
  have hli : LinearIndependent K (fun s => eS T s) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have h1 := congrArg (fun x => x * eS T t) hc
    simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h1
    rw [Finset.sum_eq_single t] at h1
    · rw [eS_idem] at h1
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (eS_ne_zero T t)
    · intro s _ hs; rw [eS_orth T s t hs, smul_zero]
    · simp
  have hv : LinearIndependent K v := LinearIndependent.of_comp U.subtype hli
  have h1 := hv.fintype_card_le_finrank
  have h2 : finrank K U ≤ Fintype.card G := finrank_range_le_card _
  omega

lemma dim_sq_le (T : GoodSet K G) (s : T.S) :
    finrank K (T.W s) * finrank K (T.W s) ≤ Fintype.card G := by
  have hall : ∀ a : MonoidAlgebra K G,
      (T.tau s).asAlgebraHom a ∈ Submodule.span K (Set.range (T.tau s)) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => rw [Representation.asAlgebraHom_of]; exact Submodule.subset_span ⟨y, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span K (Set.range (T.tau s)) = ⊤ := by
    rw [eq_top_iff]
    intro X _
    obtain ⟨a, rfl⟩ := T.irr s X
    exact hall a
  have h1 := finrank_range_le_card (R := K) (T.tau s : G → Module.End K (T.W s))
  rw [Set.finrank, htop, finrank_top, Module.finrank_linearMap] at h1
  exact h1

theorem finrank_range_eps_mul_eS_eq_nS_mul (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V) (s : T.S) :
    finrank K (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))) =
      nS T P s * finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) := by
  obtain ⟨c, hc⟩ := trace_mul_eS T s ρ
  have hn : ∀ (Q : Pair K G), ((nS T Q s : ℕ) : K) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom (eps Q)) := by
    intro Q
    rw [nS]
    exact finrank_range_idem _ (by rw [← map_mul, eps_idem])
  have hidS : ∀ (Q : Pair K G), (eps Q * eS T s) * (eps Q * eS T s) = eps Q * eS T s :=
    fun Q => mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm
  apply Nat.cast_injective (R := K)
  rw [finrank_range_idem _ (by rw [← map_mul, hidS]), Nat.cast_mul,
    finrank_range_idem _ (by rw [← map_mul, hidS]), hc, hc, ← hn, ← hn, hM s, Nat.cast_one, mul_one, mul_comm]

lemma card_smul_eS (T : GoodSet K G) (s : T.S) :
    ((Fintype.card G : ℕ) : K) • eS T s =
      ∑ y : G, (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) •
        MonoidAlgebra.of K G y := by
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eS, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]
  congr 1
  field_simp

end Alg2

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {G : Type} [Group G] [Fintype G]

lemma sigma0 (K : Type) [Field K] [NumberField K] : Nonempty (K →+* ℂ) :=
  ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom⟩

lemma chi_integral (T : GoodSet K G) (s : T.S) (y : G) :
    IsIntegral ℤ (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y)) := by
  obtain ⟨σ⟩ := sigma0 K
  have h := (trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2
  have hd : IsIntegral ℤ (((finrank K (T.W s) : ℕ) : K)) := by
    have := isIntegral_algebraMap (R := ℤ) (A := K) (x := (finrank K (T.W s) : ℤ))
    simpa using this
  exact hd.mul h

lemma chi_norm (T : GoodSet K G) (s : T.S) (y : G) (σ : K →+* ℂ) :
    ‖σ (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y))‖ ≤
      (finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ) := by
  have h := (trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

lemma ge_apply {V : Type} [AddCommGroup V] [Module K V] (T : GoodSet K G) (ρ : Representation K G V)
    (s : T.S) (x : V) :
    ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x =
      ∑ y : G, (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x := by
  rw [card_smul_eS, map_sum, LinearMap.sum_apply]
  simp only [map_smul, Representation.asAlgebraHom_of, LinearMap.smul_apply]

lemma ge_mem (T : GoodSet K G) (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ)
    (s : T.S) (x : A.V) (hx : x ∈ A.L) :
    ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x ∈ A.L := by
  rw [ge_apply]
  refine A.L.sum_mem fun y _ => ?_
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r =
      ((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹) :=
    ⟨⟨_, chi_integral T s y⁻¹⟩, rfl⟩
  rw [← hr, algebraMap_smul]
  exact A.L.smul_mem r (hA.2.1 y x hx)

lemma ge_norm (T : GoodSet K G) (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ)
    (s : T.S) (v : InfinitePlace K) (x : A.V) :
    Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x) ≤
      ((Fintype.card G : ℝ) * ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) *
        Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
  rw [ge_apply]
  refine (normAt_sum_le' A.b A.X v _ _).trans ?_
  have hterm : ∀ y : G, Formalism.HermitianLatticesTheory.normAt A.b A.X v
      ((((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x) ≤
      ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
    intro y
    rw [normAt_smul', hA.2.2]
    exact mul_le_mul_of_nonneg_right (chi_norm T s y⁻¹ v.embedding) (Real.sqrt_nonneg _)
  refine (Finset.sum_le_sum fun y _ => hterm y).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Lat

section AlgEps

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

lemma eG_eps_eS (T : GoodSet K G) (P : Pair K G) (s : T.S) :
    eps P * eG T * (eps P * eS T s) = eps P * eS T s := by
  calc eps P * eG T * (eps P * eS T s) = eps P * (eG T * eps P) * eS T s := by simp only [mul_assoc]
    _ = eps P * (eps P * eG T) * eS T s := by rw [eG_comm]
    _ = (eps P * eps P) * (eG T * eS T s) := by simp only [mul_assoc]
    _ = eps P * eS T s := by rw [eps_idem, eG_mul_eS]

lemma eS_eps_eS (T : GoodSet K G) (P : Pair K G) (s t : T.S) :
    eS T t * (eps P * eS T s) = if s = t then eps P * eS T s else 0 := by
  rw [← mul_assoc, ← eS_comm, mul_assoc]
  split_ifs with h
  · subst h; rw [eS_idem]
  · rw [eS_orth T t s (Ne.symm h), mul_zero]

lemma eS_eps_eG (T : GoodSet K G) (P : Pair K G) (s : T.S) :
    ((Fintype.card G : ℕ) : K) • eS T s * (eps P * eG T) = eps P * eS T s * (((Fintype.card G : ℕ) : K) • eG T) := by
  rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← eS_comm, mul_assoc, eS_mul_eG]

lemma eG_eps_eG (T : GoodSet K G) (P : Pair K G) : eG T * (eps P * eG T) = eps P * eG T := by
  rw [← mul_assoc, ← eG_comm, mul_assoc, eG_idem]

end AlgEps

theorem splitBound : SplitBound := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  classical
  have hfd : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR
  set L1 := cut A ρ (eps P * eG T) A.L with hL1def
  set L1s : T.S → Submodule (𝓞 K) A.V := fun s => cut A ρ (eps P * eS T s) A.L with hL1sdef
  set Pi : Submodule (𝓞 K) (T.S → A.V) := Submodule.pi Set.univ L1s with hPidef
  set ρP := Formalism.HN.piReal (fun _ : T.S => ρR) with hρP
  set dK : ℝ := (finrank ℚ K : ℝ) with hdK
  set R : ℕ := rkT T P0 P A ρ with hRdef
  have hdK0 : 0 < dK := by rw [hdK]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hL1 : L1 ≤ A.L := inf_le_left
  have hL1s : ∀ s, L1s s ≤ A.L := fun s => inf_le_left
  have lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N :=
    fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).1
  have hrkZ : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → (Formalism.HN.rk ρR N : ℝ) = dK * (Formalism.HN.rkK N : ℝ) := by
    intro N hN
    rw [(Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).2.1]
    push_cast
    rfl
  obtain ⟨hPiLat, hPirk, hPideg, -⟩ := Formalism.HN.piSum (𝓞 K) T.S (fun _ => A.V) (fun _ => _)
    (fun _ => ρR) L1s (fun s => lat _ (hL1s s))
  have hrkK1 : Formalism.HN.rkK L1 = R := rankPart K G T P0 P hM A ρ hA
  have hrkKs : ∀ s, Formalism.HN.rkK (L1s s) = nS T P s * rS T P0 A ρ s := by
    intro s
    show rkL A (cut A ρ (eps P * eS T s) A.L) = _
    rw [rkL_cut A hA.1, finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s, rS, rkL_cut A hA.1]
  have hRsum : ((R : ℕ) : ℝ) = ∑ s, ((Formalism.HN.rkK (L1s s) : ℕ) : ℝ) := by
    rw [hRdef, rkT]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrkKs s]
    push_cast
    rfl
  have hrkPi : (Formalism.HN.rk ρP Pi : ℝ) = dK * R := by
    rw [hρP, hPidef, hPirk]
    push_cast
    rw [hRsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => hrkZ _ (hL1s s)
  have hrk1 : (Formalism.HN.rk ρR L1 : ℝ) = dK * R := by rw [hrkZ L1 hL1, hrkK1]

  have hnormP : ∀ x : T.S → A.V, ‖ρP x‖ ^ 2 = ∑ s, ‖ρR (x s)‖ ^ 2 := by
    intro x
    rw [hρP, PiLp.norm_sq_eq_of_L2]
    rfl
  have hcardS : (Fintype.card T.S : ℝ) ≤ Fintype.card G := by exact_mod_cast card_S_le T
  have hG1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hGpos : (0 : ℝ) < Fintype.card G := by linarith
  have hmemPi : ∀ x : T.S → A.V, x ∈ Pi ↔ ∀ s, x s ∈ L1s s := by
    intro x
    simp [hPidef, Submodule.mem_pi]

  let fA : (T.S → A.V) →+ A.V :=
    { toFun := fun x => ∑ s, x s
      map_zero' := by simp
      map_add' := by intro x y; simp [Finset.sum_add_distrib] }
  have hfA : ∀ x, fA x = ∑ s, x s := fun x => rfl
  have hA1 : ∀ x ∈ Pi, fA x ∈ L1 := by
    intro x hx
    rw [hmemPi] at hx
    rw [hfA]
    refine Submodule.mem_inf.mpr ⟨A.L.sum_mem fun s _ => (Submodule.mem_inf.mp (hx s)).1, ?_⟩
    show ∑ s, x s ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T))
    refine Submodule.sum_mem _ fun s _ => ?_
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp (hx s)).2
    refine ⟨ρ.asAlgebraHom (eps P * eS T s) z, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, eG_eps_eS, hz]
  have hA2 : ∀ x ∈ Pi, fA x = 0 → x = 0 := by
    intro x hx h0
    rw [hmemPi] at hx
    funext t
    have hproj : ∀ s, ρ.asAlgebraHom (eS T t) (x s) = if s = t then x s else 0 := by
      intro s
      obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp (hx s)).2
      rw [← hz, ← Module.End.mul_apply, ← map_mul, eS_eps_eS]
      split_ifs <;> simp
    have := congrArg (ρ.asAlgebraHom (eS T t)) h0
    rw [hfA, map_sum, map_zero] at this
    simp only [hproj, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hA3 : ∀ x ∈ Pi, ‖ρR (fA x)‖ ≤ Real.sqrt (Fintype.card G) * ‖ρP x‖ := by
    intro x _
    rw [hfA, map_sum]
    have h1 : ‖∑ s, ρR (x s)‖ ≤ ∑ s, ‖ρR (x s)‖ := norm_sum_le _ _
    have h2 : (∑ s, ‖ρR (x s)‖) ^ 2 ≤ (Fintype.card T.S : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ s, ρR (x s)‖ ^ 2 ≤ (Real.sqrt (Fintype.card G) * ‖ρP x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hGpos.le, hnormP]
      calc ‖∑ s, ρR (x s)‖ ^ 2 ≤ (∑ s, ‖ρR (x s)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ (Fintype.card T.S : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 := h2
        _ ≤ (Fintype.card G : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcardS (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have degA := deg_ge_of_inj ρP ρR Pi L1 hPiLat (lat L1 hL1) fA hA1 hA2
    (by exact_mod_cast hrkPi.trans hrk1.symm) (Real.sqrt (Fintype.card G)) (Real.sqrt_pos.mpr hGpos) hA3

  let fB : A.V →+ (T.S → A.V) :=
    { toFun := fun x s => ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x
      map_zero' := by funext s; simp
      map_add' := by intro x y; funext s; simp }
  have hfB : ∀ x s, fB x s = ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x := fun x s => rfl
  have hB1 : ∀ x ∈ L1, fB x ∈ Pi := by
    intro x hx
    rw [hmemPi]
    intro s
    rw [hfB]
    refine Submodule.mem_inf.mpr ⟨ge_mem T A ρ hA s x (Submodule.mem_inf.mp hx).1, ?_⟩
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp hx).2
    show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))
    refine ⟨ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eG T) z, ?_⟩
    rw [← hz, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, eS_eps_eG]
  have hB2 : ∀ x ∈ L1, fB x = 0 → x = 0 := by
    intro x hx h0
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp hx).2
    have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hes : ∀ s, ρ.asAlgebraHom (eS T s) x = 0 := by
      intro s
      have := congrFun h0 s
      rw [hfB, map_smul, LinearMap.smul_apply] at this
      exact (smul_eq_zero.mp this).resolve_left hG0
    have hx' : ρ.asAlgebraHom (eG T) x = x := by
      rw [← hz, ← Module.End.mul_apply, ← map_mul, eG_eps_eG]
    rw [← hx', eG, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun s _ => hes s
  have hB3 : ∀ x ∈ L1, ‖ρP (fB x)‖ ≤ Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖ := by
    intro x _
    have hs : ∀ s, ‖ρR (fB x s)‖ ≤ (Fintype.card G : ℝ) * (Fintype.card G : ℝ) * ‖ρR x‖ := by
      intro s
      have hds : ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) ≤ Fintype.card G := by
        exact_mod_cast dim_sq_le T s
      have h1 := realize_le A.b A.X (fun y => fB y s) ((Fintype.card G : ℝ) *
        ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) (by positivity)
        (fun v y => ge_norm T A ρ hA s v y) x
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left hds hGpos.le
    have h3 : ‖ρP (fB x)‖ ^ 2 ≤ (Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hnormP]
      calc ∑ s, ‖ρR (fB x s)‖ ^ 2 ≤ ∑ s : T.S, ((Fintype.card G : ℝ) * (Fintype.card G : ℝ) * ‖ρR x‖) ^ 2 :=
            Finset.sum_le_sum fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hs s) 2
        _ = (Fintype.card T.S : ℝ) * ((Fintype.card G : ℝ) ^ 4 * ‖ρR x‖ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
        _ ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) ^ 4 * ‖ρR x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hcardS (by positivity)
        _ = (Fintype.card G : ℝ) ^ 5 * ‖ρR x‖ ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have degB := deg_ge_of_inj ρR ρP L1 Pi (lat L1 hL1) hPiLat fB hB1 hB2
    (by exact_mod_cast hrk1.trans hrkPi.symm) (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) (by positivity) hB3

  have hconv1 := degL_eq A hA.1 L1 hL1
  have hconvs : ∑ s, degL A (L1s s) = (2 / dK) * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K := by
    rw [hρP, hPidef, hPideg, hRsum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => degL_eq A hA.1 (L1s s) (hL1s s)
  have hlogA : Real.log (Real.sqrt (Fintype.card G)) = laG G / 2 := by
    rw [Real.log_sqrt hGpos.le]; rfl
  have hlogB : Real.log (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) = 5 * laG G / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_pow]; unfold laG; push_cast; ring
  have hla : 0 ≤ laG G := Real.log_nonneg hG1
  rw [hlogA, hrkPi] at degA
  rw [hlogB, hrk1] at degB
  show |degL A L1 - ∑ s, degL A (L1s s)| ≤ 5 * laG G * (R : ℝ)
  rw [hconvs, hconv1, hrkK1]
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hexpr : (2 / dK * Formalism.HN.deg ρR L1 + (R : ℝ) * kap K) - (2 / dK * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K) =
      (2 / dK) * (Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi) := by ring
  have hD1 : -(dK * R * (laG G / 2)) ≤ Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi := by linarith
  have hD2 : Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi ≤ dK * R * (5 * laG G / 2) := by linarith
  have hc : 0 < 2 / dK := by positivity
  have e1 : (2 / dK) * (dK * R * (laG G / 2)) = R * laG G := by field_simp
  have e2 : (2 / dK) * (dK * R * (5 * laG G / 2)) = 5 * R * laG G := by field_simp
  have m1 := mul_le_mul_of_nonneg_left hD1 hc.le
  have m2 := mul_le_mul_of_nonneg_left hD2 hc.le
  rw [mul_neg, e1] at m1
  rw [e2] at m2
  have hRla : 0 ≤ R * laG G := mul_nonneg hR0 hla
  rw [hexpr, abs_le]
  constructor <;> linarith

end PI.Dv.Tr
end
end

section
noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module

section Lin

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

lemma rank_one_sandwich (p : Module.End K W) (_hp : p * p = p) (h1 : finrank K (LinearMap.range p) = 1)
    (X : Module.End K W) : ∃ c : K, p * X * p = c • p := by
  obtain ⟨w0, hw0r, hw0⟩ : ∃ w0 ∈ LinearMap.range p, w0 ≠ 0 := by
    have : LinearMap.range p ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at h1; exact zero_ne_one h1
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hline : ∀ x ∈ LinearMap.range p, ∃ c : K, x = c • w0 := by
    intro x hx
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w0, hw0r⟩ : LinearMap.range p)
      (by simpa using hw0)).mp h1 ⟨x, hx⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    simpa using this.symm
  obtain ⟨c, hc⟩ := hline (p (X w0)) ⟨_, rfl⟩
  refine ⟨c, ?_⟩
  ext w
  obtain ⟨μ, hμ⟩ := hline (p w) ⟨w, rfl⟩
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rw [hμ, map_smul, map_smul, hc, smul_smul, smul_smul, mul_comm]

lemma select {ι M : Type} [Fintype ι] [AddCommGroup M] [Module K M] (v : ι → M) (n : ℕ)
    (hn : finrank K (Submodule.span K (Set.range v)) = n) :
    ∃ a : Fin n → ι, LinearIndependent K (v ∘ a) ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent'.{0} K v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    rw [← finrank_span_eq_card hli, hsp, hn]
  let e : Fin n ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_, ?_⟩
  · exact hli.comp e e.injective
  · rw [← hsp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨e.symm k, by simp⟩

lemma unit_vec {n : ℕ} {V : Type} [AddCommGroup V] [Module K V] (N : Matrix (Fin n) (Fin n) K) (hN : IsUnit N)
    (y : Fin n → V) (h : ∀ j, ∑ i, N j i • y i = 0) : y = 0 := by
  classical
  funext i
  have hinv : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul N ((Matrix.isUnit_iff_isUnit_det N).mp hN)
  calc y i = ∑ k, (1 : Matrix (Fin n) (Fin n) K) i k • y k := by simp [Matrix.one_apply]
    _ = ∑ k, (N⁻¹ * N) i k • y k := by rw [hinv]
    _ = ∑ j, N⁻¹ i j • ∑ k, N j k • y k := by
        simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
    _ = 0 := by simp [h]

lemma exists_map_to (w0 w : W) (hw0 : w0 ≠ 0) : ∃ X : Module.End K W, X w0 = w := by
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual K W, f w0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w0).mp h)
  refine ⟨((f w0)⁻¹ • f).smulRight w, ?_⟩
  rw [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf, one_smul]

end Lin

section GrpAlg

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem choose_gh (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (hM : nS T P0 s = 1) :
    ∃ (cB : MonoidAlgebra K G → K) (g h : Fin (nS T P s) → G),
      (∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s)) ∧
      IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))) := by
  classical
  set n := nS T P s with hn
  set τ := (T.tau s).asAlgebraHom with hτ
  set p := τ (eps P0) with hpdef
  have hp : p * p = p := by rw [hpdef, ← map_mul, eps_idem]
  have h1 : finrank K (LinearMap.range p) = 1 := hM
  choose cB hcB using fun a : MonoidAlgebra K G => rank_one_sandwich p hp h1 (τ a)
  have hcB' : ∀ a, τ (eps P0 * a * eps P0) = cB a • p := fun a => by
    rw [map_mul, map_mul]; exact hcB a
  have hlift : ∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s) := by
    intro a
    rw [mul_eS, hcB', map_smul, ← mul_eS]
  refine ⟨cB, ?_⟩
  obtain ⟨w0, hw0r, hw0⟩ : ∃ w0 ∈ LinearMap.range p, w0 ≠ 0 := by
    have : LinearMap.range p ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at h1; exact zero_ne_one h1
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hpw0 : p w0 = w0 := by
    obtain ⟨y, rfl⟩ := hw0r
    rw [← Module.End.mul_apply, hp]
  set u : G → T.W s := fun g => τ (eps P * MonoidAlgebra.of K G g) w0 with hu
  have hallu : ∀ a, τ (eps P * a) w0 ∈ Submodule.span K (Set.range u) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => exact Submodule.subset_span ⟨y, rfl⟩
    | add x y hx hy => rw [mul_add, map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
    | smul r x hx => rw [mul_smul_comm, map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hx
  have hspanu : Submodule.span K (Set.range u) = LinearMap.range (τ (eps P)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact ⟨τ (MonoidAlgebra.of K G y) w0, by rw [hu]; simp only [map_mul, Module.End.mul_apply]⟩
    · rintro _ ⟨w, rfl⟩
      obtain ⟨X, hX⟩ := exists_map_to (K := K) w0 w hw0
      obtain ⟨a, rfl⟩ := T.irr s X
      rw [← hX, ← Module.End.mul_apply, ← map_mul]
      exact hallu a
  have hfinu : finrank K (Submodule.span K (Set.range u)) = n := by rw [hspanu]; rfl
  obtain ⟨g, hgli, -⟩ := select u n hfinu
  set r : G → (Fin n → K) := fun h i => cB (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)) with hr
  have hkey : ∀ h i, p (τ (MonoidAlgebra.of K G h) (u (g i))) =
      cB (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)) • w0 := by
    intro h i
    have := congrArg (fun X : Module.End K (T.W s) => X w0)
      (hcB' (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)))
    simp only [LinearMap.smul_apply, hpw0] at this
    rw [← this, hu]
    simp only [map_mul, Module.End.mul_apply]
    rw [← hpdef, hpw0]
  have hspanr : Submodule.span K (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨ψ, hψ0, hψ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    set lam : Fin n → K := fun i => ψ (fun j => if i = j then 1 else 0) with hlam
    have hψr : ∀ h, ∑ i, r h i * lam i = 0 := by
      intro h
      have hmem : ψ (r h) ∈ (Submodule.span K (Set.range r)).map ψ :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨h, rfl⟩)
      rw [hψ, Submodule.mem_bot] at hmem
      rw [LinearMap.pi_apply_eq_sum_univ ψ (r h)] at hmem
      simpa [smul_eq_mul, hlam] using hmem
    set u' := ∑ i, lam i • u (g i) with hu'
    have hpu : ∀ a, p (τ a u') = 0 := by
      intro a
      induction a using MonoidAlgebra.induction_on with
      | of h =>
        rw [hu', map_sum, map_sum]
        simp only [map_smul, hkey, smul_smul]
        rw [← Finset.sum_smul]
        have : ∑ i, lam i * cB (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)) = 0 := by
          rw [← hψr h]; refine Finset.sum_congr rfl fun i _ => ?_; rw [hr]; ring
        rw [this, zero_smul]
      | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, add_zero]
      | smul c x hx => rw [map_smul, LinearMap.smul_apply, map_smul, hx, smul_zero]
    have hu'0 : u' = 0 := by
      by_contra hne'
      obtain ⟨X, hX⟩ := exists_map_to (K := K) u' w0 hne'
      obtain ⟨a, rfl⟩ := T.irr s X
      have := hpu a
      rw [hX, hpw0] at this
      exact hw0 this
    have hlam0 : lam = 0 := by
      have := (Fintype.linearIndependent_iff.mp hgli) lam (by
        have h0 := hu'0
        rw [hu'] at h0
        simpa [Function.comp_apply] using h0)
      funext i; exact this i
    apply hψ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ ψ x]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ψ (fun j => if i = j then 1 else 0) = 0 := congrFun hlam0 i
    rw [this, smul_zero]
  have hfinr : finrank K (Submodule.span K (Set.range r)) = n := by
    rw [hspanr, finrank_top, Module.finrank_fin_fun]
  obtain ⟨h, hhli, -⟩ := select r n hfinr
  refine ⟨g, h, hlift, ?_⟩
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hhli

end GrpAlg

end PI.Dv.Tr
end
end

section
noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section VLevel

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

lemma mem_range_idem {V : Type} [AddCommGroup V] [Module K V] (f : Module.End K V) (hf : f * f = f) (x : V) :
    x ∈ LinearMap.range f ↔ f x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [← Module.End.mul_apply, hf]
  · intro h; exact ⟨x, h⟩

variable (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (cB : MonoidAlgebra K G → K)
  (g h : Fin (nS T P s) → G)
  (hlift : ∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s))
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)

include hlift in
lemma key_scalar (a : MonoidAlgebra K G) (y : V) (hy : y ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) :
    ρ.asAlgebraHom (eps P0 * a) y = cB a • y := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Module.End.mul_apply, ← map_mul]
  have : eps P0 * a * (eps P0 * eS T s) = eps P0 * a * eps P0 * eS T s := by simp only [mul_assoc]
  rw [this, hlift, map_smul, LinearMap.smul_apply]

include hlift in
lemma inj_phi (hN : IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))))
    (y : Fin (nS T P s) → V) (hy : ∀ i, y i ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s)))
    (h0 : ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) (y i) = 0) : y = 0 := by
  apply unit_vec _ hN y
  intro j
  have := congrArg (ρ.asAlgebraHom (eps P0 * MonoidAlgebra.of K G (h j))) h0
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.mul_apply, ← map_mul,
    show eps P0 * MonoidAlgebra.of K G (h j) * (eps P * MonoidAlgebra.of K G (g i)) =
      eps P0 * (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i)) by simp only [mul_assoc],
    key_scalar T s P0 cB hlift ρ _ _ (hy i)]
  rfl

include hlift in
lemma inj_psi (hM : M1 T P0) [FiniteDimensional K V]
    (hN : IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))))
    (x : V) (hx : x ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s)))
    (h0 : ∀ j, ρ.asAlgebraHom (eps P0 * MonoidAlgebra.of K G (h j)) x = 0) : x = 0 := by
  classical
  set E0 := ρ.asAlgebraHom (eps P0 * eS T s) with hE0
  set Ep := ρ.asAlgebraHom (eps P * eS T s) with hEp
  have hidem : ∀ Q : Pair K G, ρ.asAlgebraHom (eps Q * eS T s) * ρ.asAlgebraHom (eps Q * eS T s) =
      ρ.asAlgebraHom (eps Q * eS T s) := fun Q => by
    rw [← map_mul, mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm]
  have he : ∀ y ∈ LinearMap.range E0, ρ.asAlgebraHom (eS T s) y = y := by
    rintro _ ⟨z, rfl⟩
    rw [hE0, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eS_comm, mul_assoc, eS_idem]
  have hmemΦ : ∀ (y : Fin (nS T P s) → LinearMap.range E0),
      ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) ((y i : LinearMap.range E0) : V) ∈
        LinearMap.range Ep := by
    intro y
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mem_range_idem Ep (hidem P)]
    conv_rhs => rw [← he _ (y i).2]
    rw [hEp, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    calc eps P * eS T s * (eps P * MonoidAlgebra.of K G (g i))
        = eps P * ((eps P * MonoidAlgebra.of K G (g i)) * eS T s) := by rw [mul_assoc, eS_comm]
      _ = (eps P * eps P) * MonoidAlgebra.of K G (g i) * eS T s := by simp only [mul_assoc]
      _ = eps P * MonoidAlgebra.of K G (g i) * eS T s := by rw [eps_idem]
  let Φ : (Fin (nS T P s) → LinearMap.range E0) →ₗ[K] LinearMap.range Ep :=
    { toFun := fun y => ⟨_, hmemΦ y⟩
      map_add' := by
        intro y z; apply Subtype.ext
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c y; apply Subtype.ext
        simp [Finset.smul_sum] }
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := congrArg Subtype.val hy
    have := inj_phi T s P0 P cB g h hlift ρ hN (fun i => ((y i : LinearMap.range E0) : V))
      (fun i => (y i).2) h1
    funext i
    apply Subtype.ext
    exact congrFun this i
  have hdim : finrank K (Fin (nS T P s) → LinearMap.range E0) = finrank K (LinearMap.range Ep) := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hEp,
      finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s]
  have hΦsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦinj
  obtain ⟨y, hy⟩ := hΦsurj ⟨x, hx⟩
  have hxy : x = ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) ((y i : LinearMap.range E0) : V) :=
    (congrArg Subtype.val hy).symm
  have hsum0 : ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) ((y i : LinearMap.range E0) : V) = 0 := by

    have hz : (fun i => ((y i : LinearMap.range E0) : V)) = 0 := by
      apply unit_vec _ hN
      intro j
      have := h0 j
      rw [hxy, map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Module.End.mul_apply, ← map_mul,
        show eps P0 * MonoidAlgebra.of K G (h j) * (eps P * MonoidAlgebra.of K G (g i)) =
          eps P0 * (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i)) by simp only [mul_assoc],
        key_scalar T s P0 cB hlift ρ _ _ (y i).2]
      rfl
    have hzi : ∀ i, ((y i : LinearMap.range E0) : V) = 0 := fun i => congrFun hz i
    simp only [hzi, map_zero, Finset.sum_const_zero]
  rw [hxy, hsum0]

end VLevel

end PI.Dv.Tr
end
end

section
noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section Helpers

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

open Classical in
lemma epsSum_mem (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ) (Q : Pair K G) (g : G)
    (y : A.V) (hy : y ∈ A.L) : ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y ∈ A.L := by
  rw [phi_apply]
  refine A.L.sum_mem fun h _ => ?_
  have hint : IsIntegral ℤ ((((Q.chi h)⁻¹ : Kˣ) : K)) :=
    IsIntegral.of_pow Fintype.card_pos (by rw [chi_pow]; exact isIntegral_one)
  have hmem : ρ (h : G) (ρ g y) ∈ A.L := hA.2.1 _ _ (hA.2.1 _ _ hy)
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (((Q.chi h)⁻¹ : Kˣ) : K) := ⟨⟨_, hint⟩, rfl⟩
  rw [← hr, algebraMap_smul]
  exact A.L.smul_mem r hmem

open Classical in
lemma epsSum_norm (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ) (Q : Pair K G) (g : G)
    (v : InfinitePlace K) (y : A.V) :
    Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y) ≤
      (Fintype.card Q.H : ℝ) * Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
  rw [phi_apply]
  refine (normAt_sum_le' A.b A.X v _ _).trans (le_of_eq ?_)
  have hterm : ∀ h : Q.H, Formalism.HermitianLatticesTheory.normAt A.b A.X v ((((Q.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y)) =
      Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
    intro h
    rw [normAt_smul', hA.2.2, hA.2.2]
    have hn : ‖v.embedding ((((Q.chi h)⁻¹ : Kˣ) : K))‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, chi_pow, map_one]) Fintype.card_ne_zero
    rw [hn, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open Classical in
lemma epsSum_apply_smul {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (Q : Pair K G) (g : G)
    (y : V) : ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y =
      ((Fintype.card Q.H : ℕ) : K) • ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y := by
  rw [epsSum_eq, smul_mul_assoc, map_smul, LinearMap.smul_apply]

end Helpers

section Ranges

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)

lemma e_fix (Q : Pair K G) (y : V) (hy : y ∈ LinearMap.range (ρ.asAlgebraHom (eps Q * eS T s))) :
    ρ.asAlgebraHom (eS T s) y = y := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eS_comm, mul_assoc, eS_idem]

lemma move_range (Q _Q' : Pair K G) (g : G) (y : V) (hy : ρ.asAlgebraHom (eS T s) y = y) :
    ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y ∈ LinearMap.range (ρ.asAlgebraHom (eps Q * eS T s)) := by
  refine ⟨ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y, ?_⟩
  conv_rhs => rw [← hy]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  calc eps Q * eS T s * (eps Q * MonoidAlgebra.of K G g)
      = eps Q * ((eps Q * MonoidAlgebra.of K G g) * eS T s) := by rw [mul_assoc, eS_comm]
    _ = (eps Q * eps Q) * MonoidAlgebra.of K G g * eS T s := by simp only [mul_assoc]
    _ = eps Q * MonoidAlgebra.of K G g * eS T s := by rw [eps_idem]

end Ranges

set_option maxHeartbeats 1000000 in

theorem perSBound : PerSBound := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA s
  classical
  have hfd : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR
  set n := nS T P s with hndef
  set r0 := rS T P0 A ρ s with hr0def
  set L1s := cut A ρ (eps P * eS T s) A.L with hL1sdef
  set L0s := cut A ρ (eps P0 * eS T s) A.L with hL0sdef
  set dK : ℝ := (finrank ℚ K : ℝ) with hdK
  have hdK0 : 0 < dK := by rw [hdK]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hL1s : L1s ≤ A.L := inf_le_left
  have hL0s : L0s ≤ A.L := inf_le_left
  have lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N :=
    fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).1
  have hrkZ : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → (Formalism.HN.rk ρR N : ℝ) = dK * (Formalism.HN.rkK N : ℝ) := by
    intro N hN
    rw [(Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).2.1]
    push_cast
    rfl
  have hrk1 : Formalism.HN.rkK L1s = n * r0 := by
    show rkL A (cut A ρ (eps P * eS T s) A.L) = _
    rw [rkL_cut A hA.1, finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s, hr0def, rS, rkL_cut A hA.1]
  have hrk0 : Formalism.HN.rkK L0s = r0 := rfl
  by_cases hn0 : n = 0
  · have h1 : degL A L1s = 0 := by
      unfold degL; rw [hrk1, hn0, zero_mul, Nat.cast_zero, zero_mul]
    rw [h1, hn0]
    simp
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  obtain ⟨cB, g, h, hlift, hN⟩ := choose_gh T s P0 P (hM s)
  set Pi0 : Submodule (𝓞 K) (Fin n → A.V) := Submodule.pi Set.univ (fun _ => L0s) with hPi0
  set ρP := Formalism.HN.piReal (fun _ : Fin n => ρR) with hρP
  obtain ⟨hPiLat, hPirk, hPideg, -⟩ := Formalism.HN.piSum (𝓞 K) (Fin n) (fun _ => A.V) (fun _ => _)
    (fun _ => ρR) (fun _ => L0s) (fun _ => lat _ hL0s)
  have hnormP : ∀ x : Fin n → A.V, ‖ρP x‖ ^ 2 = ∑ j, ‖ρR (x j)‖ ^ 2 := by
    intro x
    rw [hρP, PiLp.norm_sq_eq_of_L2]
    rfl
  have hcoord : ∀ (x : Fin n → A.V) j, ‖ρR (x j)‖ ≤ ‖ρP x‖ := by
    intro x j
    have h1 : ‖ρR (x j)‖ ^ 2 ≤ ‖ρP x‖ ^ 2 := by
      rw [hnormP]
      exact Finset.single_le_sum (f := fun j => ‖ρR (x j)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hmemPi : ∀ x : Fin n → A.V, x ∈ Pi0 ↔ ∀ j, x j ∈ L0s := by
    intro x; simp [hPi0, Submodule.mem_pi]
  have hHpos : (0 : ℝ) < Fintype.card P.H := by exact_mod_cast Fintype.card_pos
  have hH0pos : (0 : ℝ) < Fintype.card P0.H := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hHK : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hH0K : ((Fintype.card P0.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

  let fΦ : (Fin n → A.V) →+ A.V :=
    { toFun := fun y => ∑ i, ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i)
      map_zero' := by simp
      map_add' := by intro y z; simp [Finset.sum_add_distrib] }
  have hfΦ : ∀ y, fΦ y = ∑ i, ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i) := fun y => rfl
  have hΦ1 : ∀ y ∈ Pi0, fΦ y ∈ L1s := by
    intro y hy
    rw [hmemPi] at hy
    rw [hfΦ]
    refine Submodule.mem_inf.mpr ⟨A.L.sum_mem fun i _ => epsSum_mem A ρ hA P (g i) _ (Submodule.mem_inf.mp (hy i)).1, ?_⟩
    show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [epsSum_apply_smul]
    exact Submodule.smul_mem _ _ (move_range T s ρ P P0 (g i) (y i)
      (e_fix T s ρ P0 (y i) (Submodule.mem_inf.mp (hy i)).2))
  have hΦ2 : ∀ y ∈ Pi0, fΦ y = 0 → y = 0 := by
    intro y hy h0
    rw [hmemPi] at hy
    rw [hfΦ] at h0
    simp only [epsSum_apply_smul, ← Finset.smul_sum] at h0
    have h0' := (smul_eq_zero.mp h0).resolve_left hHK
    exact inj_phi T s P0 P cB g h hlift ρ hN y (fun i => (Submodule.mem_inf.mp (hy i)).2) h0'
  have hΦ3 : ∀ y ∈ Pi0, ‖ρR (fΦ y)‖ ≤ ((n : ℝ) * Fintype.card P.H) * ‖ρP y‖ := by
    intro y _
    rw [hfΦ, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i, ‖ρR (ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i))‖ ≤
        (Fintype.card P.H : ℝ) * ‖ρP y‖ := by
      intro i
      refine (realize_le A.b A.X (fun z => ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) z)
        (Fintype.card P.H : ℝ) hHpos.le (fun v z => epsSum_norm A ρ hA P (g i) v z) (y i)).trans ?_
      exact mul_le_mul_of_nonneg_left (hcoord y i) hHpos.le
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

  let fΨ : A.V →+ (Fin n → A.V) :=
    { toFun := fun x j => ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) x
      map_zero' := by funext j; simp
      map_add' := by intro x y; funext j; simp }
  have hfΨ : ∀ x j, fΨ x j = ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) x := fun x j => rfl
  have hΨ1 : ∀ x ∈ L1s, fΨ x ∈ Pi0 := by
    intro x hx
    rw [hmemPi]
    intro j
    rw [hfΨ]
    refine Submodule.mem_inf.mpr ⟨epsSum_mem A ρ hA P0 (h j) x (Submodule.mem_inf.mp hx).1, ?_⟩
    show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))
    rw [epsSum_apply_smul]
    exact Submodule.smul_mem _ _ (move_range T s ρ P0 P (h j) x (e_fix T s ρ P x (Submodule.mem_inf.mp hx).2))
  have hΨ2 : ∀ x ∈ L1s, fΨ x = 0 → x = 0 := by
    intro x hx h0
    refine inj_psi T s P0 P cB g h hlift ρ hM hN x (Submodule.mem_inf.mp hx).2 fun j => ?_
    have := congrFun h0 j
    rw [hfΨ, epsSum_apply_smul] at this
    exact (smul_eq_zero.mp this).resolve_left hH0K
  have hΨ3 : ∀ x ∈ L1s, ‖ρP (fΨ x)‖ ≤ ((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖ := by
    intro x _
    have hj : ∀ j, ‖ρR (fΨ x j)‖ ≤ (Fintype.card P0.H : ℝ) * ‖ρR x‖ := fun j =>
      realize_le A.b A.X (fun z => ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) z)
        (Fintype.card P0.H : ℝ) hH0pos.le (fun v z => epsSum_norm A ρ hA P0 (h j) v z) x
    have h3 : ‖ρP (fΨ x)‖ ^ 2 ≤ (((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖) ^ 2 := by
      rw [hnormP]
      calc ∑ j, ‖ρR (fΨ x j)‖ ^ 2 ≤ ∑ j : Fin n, ((Fintype.card P0.H : ℝ) * ‖ρR x‖) ^ 2 :=
            Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hj j) 2
        _ = (n : ℝ) * ((Fintype.card P0.H : ℝ) * ‖ρR x‖) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (n : ℝ) ^ 2 * ((Fintype.card P0.H : ℝ) * ‖ρR x‖) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
            nlinarith
        _ = (((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

  have hrkPi : (Formalism.HN.rk ρP Pi0 : ℝ) = dK * ((n * r0 : ℕ) : ℝ) := by
    rw [hρP, hPi0, hPirk]
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hrkZ L0s hL0s, hrk0]
    ring
  have hrkL1 : (Formalism.HN.rk ρR L1s : ℝ) = dK * ((n * r0 : ℕ) : ℝ) := by rw [hrkZ L1s hL1s, hrk1]
  have hdegPi : Formalism.HN.deg ρP Pi0 = (n : ℝ) * Formalism.HN.deg ρR L0s := by
    rw [hρP, hPi0, hPideg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have degΦ := deg_ge_of_inj ρP ρR Pi0 L1s hPiLat (lat L1s hL1s) fΦ hΦ1 hΦ2
    (by exact_mod_cast hrkPi.trans hrkL1.symm) ((n : ℝ) * Fintype.card P.H) (by positivity) hΦ3
  have degΨ := deg_ge_of_inj ρR ρP L1s Pi0 (lat L1s hL1s) hPiLat fΨ hΨ1 hΨ2
    (by exact_mod_cast hrkL1.trans hrkPi.symm) ((n : ℝ) * Fintype.card P0.H) (by positivity) hΨ3
  rw [hrkPi, hdegPi] at degΦ
  rw [hrkL1, hdegPi] at degΨ

  have hG1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hla : 0 ≤ laG G := Real.log_nonneg hG1
  have hnG : (n : ℝ) ≤ Fintype.card G := by
    have h1 : n ≤ finrank K (T.W s) := Submodule.finrank_le _
    have h2 := dim_sq_le T s
    have h3 : finrank K (T.W s) ≤ finrank K (T.W s) * finrank K (T.W s) := Nat.le_mul_self _
    exact_mod_cast h1.trans (h3.trans h2)
  have hHG : (Fintype.card P.H : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_subtype_le _
  have hH0G : (Fintype.card P0.H : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_subtype_le _
  have hlog1 : Real.log ((n : ℝ) * Fintype.card P.H) ≤ 2 * laG G := by
    rw [Real.log_mul hnpos.ne' hHpos.ne']
    have a1 := Real.log_le_log hnpos hnG
    have a2 := Real.log_le_log hHpos hHG
    unfold laG; linarith
  have hlog2 : Real.log ((n : ℝ) * Fintype.card P0.H) ≤ 2 * laG G := by
    rw [Real.log_mul hnpos.ne' hH0pos.ne']
    have a1 := Real.log_le_log hnpos hnG
    have a2 := Real.log_le_log hH0pos hH0G
    unfold laG; linarith

  have hc1 := degL_eq A hA.1 L1s hL1s
  have hc0 := degL_eq A hA.1 L0s hL0s
  rw [hrk1] at hc1
  rw [hrk0] at hc0
  set R0 : ℝ := ((n * r0 : ℕ) : ℝ) with hR0
  have hR0nn : 0 ≤ R0 := Nat.cast_nonneg _
  have hexpr : degL A L1s - (n : ℝ) * degL A L0s =
      (2 / dK) * (Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s) := by
    rw [hc1, hc0, hR0]
    push_cast
    ring
  have hD1 : -(dK * R0 * (2 * laG G)) ≤ Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s := by
    have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ dK * R0)
    linarith
  have hD2 : Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s ≤ dK * R0 * (2 * laG G) := by
    have := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ dK * R0)
    linarith
  have hc : 0 < 2 / dK := by positivity
  have e1 : (2 / dK) * (dK * R0 * (2 * laG G)) = 4 * R0 * laG G := by field_simp; ring
  have m1 := mul_le_mul_of_nonneg_left hD1 hc.le
  have m2 := mul_le_mul_of_nonneg_left hD2 hc.le
  rw [mul_neg, e1] at m1
  rw [e1] at m2
  have hRla : 0 ≤ R0 * laG G := mul_nonneg hR0nn hla
  show |degL A L1s - (n : ℝ) * degL A L0s| ≤ 5 * laG G * R0
  rw [hexpr, abs_le]
  constructor <;> linarith

end PI.Dv.Tr
end
end

section
namespace PI.Dv.Tr

theorem degPart : DegPart := degPart_of splitBound perSBound


end PI.Dv.Tr
end
