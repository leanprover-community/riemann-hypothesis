import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemTer

section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem idx_self (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) : idxAt w M M = 0 := sub_self _


theorem one_notMem_w (w : HeightOneSpectrum (𝓞 K)) : (1 : 𝓞 K) ∉ w.asIdeal :=
  fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem idx_chain (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N P : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (hP : P.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (h2 : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P :=
  (hI K V w M N hM hN h1).2.1 P hP h2

theorem idx_nonneg_of_le (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (hle : N ≤ M) :
    0 ≤ idxAt w M N := by
  have := (hI K V w M N hM hN h1).2.2.2.1 0 (fun x hx => ⟨1, one_notMem_w w, by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, one_smul]; exact hle hx⟩)
  simpa using this

theorem idx_le_nat (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (n : ℕ) (hn : 0 < n)
    (hle : N ≤ M) (hsm : ∀ x ∈ M, ((n : ℕ) : 𝓞 K) • x ∈ N) :
    idxAt w M N ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((n : ℕ) : K) :=
  (hI K V w M N hM hN h1).2.2.2.2.2 n hn hle hsm

theorem idx_map (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hker : M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  have := (hI K V w M N hM hN h1).2.2.1 V' φ
  rw [hker, idx_self, zero_add] at this
  exact this

theorem idx_map_inj (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hinjM : ∀ x ∈ M, φ x = 0 → x = 0) (hinjN : ∀ x ∈ N, φ x = 0 → x = 0) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  refine idx_map hI w φ M N hM hN h1 ?_
  have hb : ∀ P : Submodule (𝓞 K) V, (∀ x ∈ P, φ x = 0 → x = 0) →
      P ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    intro P hP
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (Submodule.mem_bot _).mpr (hP x hx1 hx2)
  rw [hb M hinjM, hb N hinjN]

theorem span_pi_eq {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V) :
    Submodule.span K ((Submodule.pi Set.univ M : Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
      Submodule.pi Set.univ (fun i => Submodule.span K (M i : Set V)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx i _
    exact Submodule.subset_span (hx i (Set.mem_univ i))
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro m hm
    rw [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    intro j _
    by_cases h : j = i
    · subst h; simpa using hm
    · simp [h]

theorem idx_pi (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M N : ι → Submodule (𝓞 K) V) (hM : ∀ i, (M i).FG) (hN : ∀ i, (N i).FG)
    (hsp : ∀ i, Submodule.span K (M i : Set V) = Submodule.span K (N i : Set V)) :
    idxAt w (Submodule.pi Set.univ M) (Submodule.pi Set.univ N) = ∑ i, idxAt w (M i) (N i) := by
  have key : ∀ s : Finset ι, idxAt w (Submodule.pi Set.univ fun i => if i ∈ s then M i else ⊥)
      (Submodule.pi Set.univ fun i => if i ∈ s then N i else ⊥) = ∑ i ∈ s, idxAt w (M i) (N i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [idx_self]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← ih]
      have fg : ∀ P : ι → Submodule (𝓞 K) V, (∀ i, (P i).FG) →
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).FG := fun P hP =>
        Submodule.fg_pi fun i => by split_ifs; exacts [hP i, Submodule.fg_bot]
      have sp : Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then M i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
          Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then N i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) := by
        rw [span_pi_eq, span_pi_eq]
        congr 1; funext i; split_ifs
        · exact hsp i
        · simp
      have hc := (hI K (ι → V) w _ _ (fg M hM) (fg N hN) sp).2.2.1 V (LinearMap.proj a)
      have hker : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥) ⊓
            (LinearMap.ker (LinearMap.proj a : (ι → V) →ₗ[K] V)).restrictScalars (𝓞 K) =
          Submodule.pi Set.univ fun i => if i ∈ s then P i else ⊥ := by
        intro P
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ, true_implies,
          Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.proj_apply]
        constructor
        · rintro ⟨h1, h2⟩ i
          by_cases hi : i = a
          · subst hi; simp [ha, h2]
          · have := h1 i; simpa [Finset.mem_insert, hi] using this
        · intro h
          refine ⟨fun i => ?_, ?_⟩
          · by_cases hi : i = a
            · subst hi; have := h i; simp only [ha, if_false, Submodule.mem_bot] at this; simp [this]
            · have := h i; simpa [Finset.mem_insert, hi] using this
          · have := h a; simpa [ha] using this
      have hmap : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).map
            ((LinearMap.proj a : (ι → V) →ₗ[K] V).restrictScalars (𝓞 K)) = P a := by
        intro P
        ext m
        simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
          LinearMap.coe_restrictScalars, LinearMap.proj_apply]
        constructor
        · rintro ⟨x, hx, rfl⟩; have := hx a; simpa using this
        · intro hm
          refine ⟨Pi.single a m, fun i => ?_, by simp⟩
          by_cases hi : i = a
          · subst hi; simpa using hm
          · simp [hi]
      rw [hc, hker, hker, hmap, hmap, add_comm]
  simpa using key Finset.univ

end Gen

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero

private theorem log_nonpos_of_le_one (m : ℤᵐ⁰) (h : m ≤ 1) : WithZero.log m ≤ 0 := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0, WithZero.log_zero]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero] at h
    exact WithZero.exp_le_exp.mp h

theorem volume_nonneg : VNonneg := by
  intro K _ _ w x
  unfold vAdd
  have h := log_nonpos_of_le_one (w.valuation K (algebraMap (𝓞 K) K x)) (w.valuation_le_one x)
  omega



theorem unzero_toAdd (m : ℤᵐ⁰) (h : m ≠ 0) : Multiplicative.toAdd (WithZero.unzero h) = WithZero.log m := by
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
  first
  | rfl
  | simp [WithZero.log]
  | simp

theorem norm_embedding_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(vAdd v x)) := by
  have hv : v.valuation K x ≠ 0 := by simpa using hx
  have he : Valued.v (FinitePlace.embedding v x) = v.valuation K x := by
    first
    | exact v.valuedAdicCompletion_eq_valuation' x
    | exact v.valuedAdicCompletion_eq_valuation x
    | rfl
  rw [FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ hv, unzero_toAdd _ hv]
  simp [vAdd]



theorem abs_norm_le {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ) (hB : 0 ≤ B)
    (hσ : ∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) :
    |((Algebra.norm ℤ x : ℤ) : ℝ)| ≤ B ^ Module.finrank ℚ K := by
  have h1 : |((Algebra.norm ℤ x : ℤ) : ℝ)| =
      ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K x) ^ w.mult := by
    rw [InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
    first
    | simp
    | norm_cast
  rw [h1, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _) (fun w _ => ?_)
  refine pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) ?_ _
  rw [← InfinitePlace.norm_embedding_eq]
  exact hσ _


end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Vals

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mul (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  have hx' : w.valuation K x ≠ 0 := by simpa using hx
  have hy' : w.valuation K y ≠ 0 := by simpa using hy
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

theorem vAdd_prod (w : HeightOneSpectrum (𝓞 K)) {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vAdd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vAdd_mul w _ _ (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem mem_pow_of_vAdd (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    a ∈ w.asIdeal ^ (vAdd w (algebraMap (𝓞 K) K a)).toNat := by
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
  have h0 : w.valuation K (algebraMap (𝓞 K) K a) ≠ 0 := by simpa using ha
  have hnn := volume_nonneg K w a
  rw [Int.toNat_of_nonneg hnn]
  unfold vAdd
  rw [neg_neg, WithZero.exp_log h0]

end Vals

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def smulSub (d : K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  L.map ((d • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K))

theorem mem_smulSub (d : K) (L : Submodule (𝓞 K) V) (x : V) : x ∈ smulSub d L ↔ ∃ y ∈ L, d • y = x := by
  simp [smulSub]

theorem span_smulSub (d : K) (hd : d ≠ 0) (L : Submodule (𝓞 K) V) :
    Submodule.span K (smulSub d L : Set V) = Submodule.span K (L : Set V) := by
  rw [smulSub, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using Submodule.smul_mem _ d hy
  · intro hx
    refine ⟨d⁻¹ • x, Submodule.smul_mem _ _ hx, ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hd]

theorem smulSub_smulSub (d e : K) (L : Submodule (𝓞 K) V) : smulSub d (smulSub e L) = smulSub (d * e) L := by
  ext x
  simp only [mem_smulSub]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, by rw [smul_smul]⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨e • z, ⟨z, hz, rfl⟩, by rw [smul_smul]⟩

theorem fg_smulSub (d : K) (L : Submodule (𝓞 K) V) (hL : L.FG) : (smulSub d L).FG := hL.map _

theorem idx_smulSub_map (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M N : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) :
    idxAt w (smulSub d M) (smulSub d N) = idxAt w M N := by
  have hinj : ∀ P : Submodule (𝓞 K) V, ∀ x ∈ P, (d • LinearMap.id : V →ₗ[K] V) x = 0 → x = 0 := by
    intro P x _ hx
    simpa [hd] using hx
  exact (idx_map_inj hI w (d • LinearMap.id) M N hM hN h1 (hinj M) (hinj N)).symm

theorem idx_ge_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    vAdd w (algebraMap (𝓞 K) K a) * (Formalism.HN.rkK M : ℤ) ≤ idxAt w M (smulSub (algebraMap (𝓞 K) K a) M) := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
  have hsp := (span_smulSub (algebraMap (𝓞 K) K a) haK M).symm
  have := (hI K V w M _ hM (fg_smulSub _ M hM) hsp).2.2.2.1 (vAdd w (algebraMap (𝓞 K) K a)).toNat
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := (mem_smulSub _ M x).mp hx
      refine ⟨1, one_notMem_w w, ?_⟩
      rw [one_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul (mem_pow_of_vAdd w a ha) hy)
  rwa [Int.toNat_of_nonneg (volume_nonneg K w a)] at this

theorem idx_le_natSub (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 0 < m)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub ((m : ℕ) : K) M) ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((m : ℕ) : K) := by
  have hmK : ((m : ℕ) : K) ≠ 0 := by exact_mod_cast hm.ne'
  refine idx_le_nat hI w M _ hM (fg_smulSub _ M hM) (span_smulSub _ hmK M).symm m hm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_smulSub _ M x).mp hx
    rw [Nat.cast_smul_eq_nsmul K m y, ← Nat.cast_smul_eq_nsmul (𝓞 K) m y]
    exact Submodule.smul_mem _ _ hy
  · intro x hx
    refine (mem_smulSub _ M _).mpr ⟨x, hx, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem idx_smulSub_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub (algebraMap (𝓞 K) K a) M) = (Formalism.HN.rkK M : ℤ) * vAdd w (algebraMap (𝓞 K) K a) := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
  have hspan : Ideal.span {a} ≠ ⊥ := by simpa using ha
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a}))
  set m := Ideal.absNorm (Ideal.span {a}) with hm
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rw [hm, Ne, Ideal.absNorm_eq_zero_iff]; exact hspan)
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha'
    exact hm0.ne' (by exact_mod_cast ha'.symm)
  have ha'K : algebraMap (𝓞 K) K a' ≠ 0 := by simpa using ha'0
  have hmK : ((m : ℕ) : K) = algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K a' := by
    rw [← map_mul, mul_comm, ha', map_natCast]
  have e1 := idx_chain hI w M (smulSub (algebraMap (𝓞 K) K a) M) (smulSub ((m : ℕ) : K) M) hM
    (fg_smulSub _ M hM) (fg_smulSub _ M hM) (span_smulSub _ haK M).symm
    (by rw [span_smulSub _ (by rw [hmK]; exact mul_ne_zero haK ha'K), span_smulSub _ haK])
  have e2 : idxAt w (smulSub (algebraMap (𝓞 K) K a) M) (smulSub ((m : ℕ) : K) M) =
      idxAt w M (smulSub (algebraMap (𝓞 K) K a') M) := by
    rw [hmK, ← smulSub_smulSub]
    exact idx_smulSub_map hI w _ haK M _ hM (fg_smulSub _ M hM) (span_smulSub _ ha'K M).symm
  have u := idx_le_natSub hI w m hm0 M hM
  have l1 := idx_ge_int hI w a ha M hM
  have l2 := idx_ge_int hI w a' ha'0 M hM
  rw [e1, e2, hmK, vAdd_mul w _ _ haK ha'K] at u
  nlinarith

theorem idx_smulSub (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub d M) = (Formalism.HN.rkK M : ℤ) * vAdd w d := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) d
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hd; rw [h, zero_div]
  have ha0 : a ≠ 0 := by intro h; apply haK; rw [h, map_zero]
  set d := algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b with hd'
  have hda : d * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a := by
    rw [hd', div_mul_cancel₀ _ hbK]
  have e1 := idx_chain hI w M (smulSub d M) (smulSub (algebraMap (𝓞 K) K a) M) hM
    (fg_smulSub _ M hM) (fg_smulSub _ M hM) (span_smulSub _ hd M).symm
    (by rw [span_smulSub _ haK, span_smulSub _ hd])
  have e2 : idxAt w (smulSub d M) (smulSub (algebraMap (𝓞 K) K a) M) =
      idxAt w M (smulSub (algebraMap (𝓞 K) K b) M) := by
    rw [← hda, ← smulSub_smulSub]
    exact idx_smulSub_map hI w _ hd M _ hM (fg_smulSub _ M hM) (span_smulSub _ hbK M).symm
  rw [e2, idx_smulSub_int hI w a ha0 M hM, idx_smulSub_int hI w b hb0 M hM] at e1
  have hv : vAdd w (algebraMap (𝓞 K) K a) = vAdd w d + vAdd w (algebraMap (𝓞 K) K b) := by
    rw [← hda, vAdd_mul w _ _ hd hbK]
  rw [hv] at e1
  linarith

end Gen

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def matV {n : Type} [Fintype n] (Γ : Matrix n n K) : (n → V) →ₗ[K] (n → V) :=
  LinearMap.pi fun k => ∑ l, Γ k l • LinearMap.proj l

theorem matV_apply {n : Type} [Fintype n] (Γ : Matrix n n K) (x : n → V) (k : n) :
    matV Γ x k = ∑ l, Γ k l • x l := by
  simp [matV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem matV_mul {n : Type} [Fintype n] (A B : Matrix n n K) :
    (matV (A * B) : (n → V) →ₗ[K] (n → V)) = matV A ∘ₗ matV B := by
  apply LinearMap.ext; intro x; funext k
  simp only [matV_apply, LinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem matV_one {n : Type} [Fintype n] [DecidableEq n] :
    (matV (1 : Matrix n n K) : (n → V) →ₗ[K] (n → V)) = LinearMap.id := by
  apply LinearMap.ext; intro x; funext k
  simp [matV_apply, Matrix.one_apply, ite_smul]

theorem matV_inv_cancel {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A (matV A⁻¹ x) = x := by
  rw [← LinearMap.comp_apply, ← matV_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), matV_one,
    LinearMap.id_apply]

theorem matV_inv_cancel' {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A⁻¹ (matV A x) = x := by
  rw [← LinearMap.comp_apply, ← matV_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), matV_one,
    LinearMap.id_apply]

theorem map_matV_pi {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (S : Submodule K V) :
    (Submodule.pi Set.univ fun _ : n => S).map (matV A) = Submodule.pi Set.univ fun _ : n => S := by
  have hsub : ∀ B : Matrix n n K, ∀ x ∈ (Submodule.pi Set.univ fun _ : n => S), matV B x ∈
      (Submodule.pi Set.univ fun _ : n => S) := by
    intro B x hx k _
    rw [matV_apply]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact hsub A x hx
  · intro x hx
    exact ⟨matV A⁻¹ x, hsub _ x hx, matV_inv_cancel A hA x⟩

def latPow (n : Type) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) (n → V) := Submodule.pi Set.univ fun _ : n => M

theorem span_latPow {n : Type} [Fintype n] [DecidableEq n] (M : Submodule (𝓞 K) V) :
    Submodule.span K ((latPow n M : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => Submodule.span K (M : Set V) :=
  span_pi_eq _

theorem span_map_matV {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0)
    (L : Submodule (𝓞 K) (n → V)) (S : Submodule K V)
    (hL : Submodule.span K (L : Set (n → V)) = Submodule.pi Set.univ fun _ : n => S) :
    Submodule.span K ((L.map ((matV A).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => S := by
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hL, map_matV_pi A hA]

theorem matV_transvection {n : Type} [Fintype n] [DecidableEq n] (i j : n) (c : K) (x : n → V) :
    matV (Matrix.transvection i j c) x = x + Pi.single i (c • x j) := by
  funext k
  rw [matV_apply]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul,
    Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Pi.add_apply]
  by_cases hk : i = k
  · subst hk; simp
  · simp [hk, Pi.single_apply, Ne.symm hk]

theorem idx_matV (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {n : Type} [Fintype n] [DecidableEq n]
    (M : Submodule (𝓞 K) V) (hM : M.FG) (A : Matrix n n K) (hA : A.det ≠ 0) :
    idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det := by
  have hLfg : (latPow n M).FG := Submodule.fg_pi fun _ => hM
  have hsp := span_latPow (n := n) M
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A => idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det) A hA ?_ ?_ ?_
  ·
    intro D hD
    have hDk : ∀ k, D k ≠ 0 := fun k => by
      rw [Matrix.det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD k (Finset.mem_univ k)
    have hmap : (latPow n M).map ((matV (Matrix.diagonal D)).restrictScalars (𝓞 K)) =
        Submodule.pi Set.univ fun k => smulSub (D k) M := by
      ext x
      simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Submodule.mem_pi, Set.mem_univ,
        true_implies, latPow, mem_smulSub]
      constructor
      · rintro ⟨y, hy, rfl⟩ k
        exact ⟨y k, hy k, by rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul]⟩
      · intro h
        choose y hy hyx using h
        exact ⟨y, hy, by funext k; rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul, hyx]⟩
    rw [hmap, latPow, idx_pi hI w _ _ (fun _ => hM) (fun k => fg_smulSub _ M hM)
      (fun k => (span_smulSub _ (hDk k) M).symm), Matrix.det_diagonal,
      vAdd_prod w _ _ (fun k _ => hDk k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => idx_smulSub hI w (D k) (hDk k) M hM
  ·
    intro t
    rw [Matrix.TransvectionStruct.toMatrix, Matrix.det_transvection_of_ne _ _ t.hij]
    have hv1 : vAdd w (1 : K) = 0 := by simp [vAdd]
    rw [hv1, mul_zero]
    set φ : (n → V) →ₗ[K] (n → V) := LinearMap.id - (LinearMap.single K (fun _ => V) t.i) ∘ₗ LinearMap.proj t.i
      with hφ
    have hφapp : ∀ x : n → V, φ x = x - Pi.single t.i (x t.i) := fun x => by simp [hφ]
    have hφT : φ ∘ₗ matV (Matrix.transvection t.i t.j t.c) = φ := by
      apply LinearMap.ext; intro x
      rw [LinearMap.comp_apply, hφapp, hφapp, matV_transvection]
      funext k
      by_cases hk : k = t.i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    have hker0 : ∀ z : n → V, φ z = 0 ↔ ∀ k, k ≠ t.i → z k = 0 := by
      intro z
      rw [hφapp]
      constructor
      · intro h k hk
        have := congrFun h k
        simpa [Pi.single_apply, hk] using this
      · intro h
        funext k
        by_cases hk : k = t.i
        · subst hk; simp
        · simp [Pi.single_apply, hk, h k hk]
    have hfix : ∀ z : n → V, φ z = 0 → matV (Matrix.transvection t.i t.j t.c) z = z := by
      intro z hz
      rw [matV_transvection, (hker0 z).mp hz t.j (Ne.symm t.hij), smul_zero, Pi.single_zero, add_zero]
    have hT := span_map_matV (Matrix.transvection t.i t.j t.c)
      (by rw [Matrix.det_transvection_of_ne _ _ t.hij]; exact one_ne_zero) (latPow n M) _ hsp
    rw [idx_map hI w φ _ _ hLfg (hLfg.map _) (by rw [hT, hsp])]
    · rw [← Submodule.map_comp]
      have : ((φ.restrictScalars (𝓞 K)).comp ((matV (Matrix.transvection t.i t.j t.c)).restrictScalars (𝓞 K))) =
          φ.restrictScalars (𝓞 K) := by
        rw [← LinearMap.restrictScalars_comp, hφT]
      rw [this, idx_self]
    · ext z
      simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_map,
        LinearMap.coe_restrictScalars]
      constructor
      · rintro ⟨hz, hz0⟩
        exact ⟨⟨z, hz, hfix z hz0⟩, hz0⟩
      · rintro ⟨⟨x, hx, rfl⟩, hz0⟩
        have hx0 : φ x = 0 := by
          rw [← hz0, ← LinearMap.comp_apply, hφT]
        rw [hfix x hx0]
        exact ⟨hx, by rw [hfix x hx0] at hz0; exact hz0⟩
  ·
    intro A B hA hB hPA hPB
    have hsB := span_map_matV B hB (latPow n M) _ hsp
    have hsA := span_map_matV A hA (latPow n M) _ hsp
    have hsAB := span_map_matV A hA _ _ hsB
    have hcomp : (latPow n M).map ((matV (A * B)).restrictScalars (𝓞 K)) =
        ((latPow n M).map ((matV B).restrictScalars (𝓞 K))).map ((matV A).restrictScalars (𝓞 K)) := by
      rw [← Submodule.map_comp, matV_mul, LinearMap.restrictScalars_comp]
    rw [hcomp, idx_chain hI w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) _ hLfg
      (hLfg.map _) ((hLfg.map _).map _) (by rw [hsA, hsp]) (by rw [hsAB, hsA])]
    have hinj : ∀ P : Submodule (𝓞 K) (n → V), ∀ x ∈ P, matV A x = 0 → x = 0 := by
      intro P x _ hx
      rw [← matV_inv_cancel' A hA x, hx, map_zero]
    rw [← idx_map_inj hI w (matV A) (latPow n M) _ hLfg (hLfg.map _) (by rw [hsB, hsp]) (hinj _) (hinj _),
      hPA, hPB, Matrix.det_mul, vAdd_mul w _ _ hA hB]
    ring

end Gen

end PI.Dv.TIW
end
end

section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Cut

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ M :=
  _root_.UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem M x hx

theorem cut_span (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Submodule.span K ((M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = X := by
  apply le_antisymm
  · rw [Submodule.span_le]; intro x hx; exact hx.2
  · intro x hx
    obtain ⟨a, ha, hax⟩ := exists_smul_mem M x (by rw [hM]; exact Submodule.mem_top)
    have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    have hmem : a • x ∈ (M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine Submodule.mem_inf.mpr ⟨hax, ?_⟩
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul K]
      exact X.smul_mem _ hx
    have : x = (algebraMap (𝓞 K) K a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ haK, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)


theorem fg_cut (M : Submodule (𝓞 K) V) (hM : M.FG) (X : Submodule K V) : (M ⊓ X.restrictScalars (𝓞 K)).FG :=
  Submodule.FG.of_le hM inf_le_left

end Cut

section Block

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ}

def Φt (Φ : Fin n → V →ₗ[K] V) : (Fin n → V) →ₗ[K] V := ∑ i, Φ i ∘ₗ LinearMap.proj i

theorem Φt_apply (Φ : Fin n → V →ₗ[K] V) (x : Fin n → V) : Φt Φ x = ∑ i, Φ i (x i) := by
  simp [Φt, LinearMap.sum_apply]

theorem Ψt_apply (Ψ : Fin n → V →ₗ[K] V) (y : V) (j : Fin n) : (LinearMap.pi Ψ) y j = Ψ j y := rfl

structure BlockHyp (X Y : Submodule K V) (Φ Ψ : Fin n → V →ₗ[K] V) (Γ : Matrix (Fin n) (Fin n) K) : Prop where
  det : Γ.det ≠ 0
  h1 : ∀ i j, ∀ x ∈ X, Ψ j (Φ i x) = Γ j i • x
  h2 : ∀ i, ∀ x ∈ X, Φ i x ∈ Y
  h3 : ∀ j, ∀ y ∈ Y, Ψ j y ∈ X
  h4 : ∀ y ∈ Y, ∃ x : Fin n → V, (∀ i, x i ∈ X) ∧ y = ∑ i, Φ i (x i)

variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}

theorem BlockHyp.psiPhi (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    LinearMap.pi Ψ (Φt Φ x) = matV Γ x := by
  funext j
  rw [Ψt_apply, Φt_apply, map_sum, matV_apply]
  exact Finset.sum_congr rfl fun i _ => H.h1 i j (x i) (hx i (Set.mem_univ i))

theorem BlockHyp.phi_mem (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    Φt Φ x ∈ Y := by
  rw [Φt_apply]
  exact Y.sum_mem fun i _ => H.h2 i _ (hx i (Set.mem_univ i))

theorem BlockHyp.psi_mem (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) :
    LinearMap.pi Ψ y ∈ Submodule.pi Set.univ fun _ : Fin n => X :=
  fun j _ => H.h3 j y hy

theorem BlockHyp.phi_inj (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X)
    (h0 : Φt Φ x = 0) : x = 0 := by
  have := H.psiPhi x hx
  rw [h0, map_zero] at this
  rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]

theorem BlockHyp.psi_inj (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) (h0 : LinearMap.pi Ψ y = 0) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := H.h4 y hy
  have hx' : x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun i _ => hx i
  have := H.psiPhi x hx'
  rw [Φt_apply] at this
  rw [h0] at this
  have hx0 : x = 0 := by rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]
  simp [hx0]

theorem BlockHyp.map_phi (H : BlockHyp X Y Φ Ψ Γ) :
    (Submodule.pi Set.univ fun _ : Fin n => X).map (Φt Φ) = Y := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact H.phi_mem x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := H.h4 y hy
    exact ⟨x, fun i _ => hx i, by rw [Φt_apply]⟩

theorem BlockHyp.map_psi (H : BlockHyp X Y Φ Ψ Γ) :
    Y.map (LinearMap.pi Ψ) = Submodule.pi Set.univ fun _ : Fin n => X := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩; exact H.psi_mem y hy
  · intro x hx
    have hx' : matV Γ⁻¹ x ∈ Submodule.pi Set.univ fun _ : Fin n => X := by
      intro k _
      rw [matV_apply]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
    refine ⟨Φt Φ (matV Γ⁻¹ x), H.phi_mem _ hx', ?_⟩
    rw [H.psiPhi _ hx', matV_inv_cancel Γ H.det]

theorem BlockHyp.finrank [FiniteDimensional K V] (H : BlockHyp X Y Φ Ψ Γ) : Module.finrank K Y = n * Module.finrank K X := by
  let f : (Fin n → X) →ₗ[K] Y := LinearMap.codRestrict Y
    (Φt Φ ∘ₗ LinearMap.pi (fun i => X.subtype ∘ₗ LinearMap.proj i))
    (fun x => H.phi_mem _ (fun i _ => (x i).2))
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply] at h
      rw [← sub_eq_zero, ← map_sub] at h
      have := H.phi_inj _ (Submodule.sub_mem _ (fun i _ => (x i).2) (fun i _ => (y i).2)) h
      funext i
      apply Subtype.ext
      have := congrFun this i
      simpa [sub_eq_zero] using this
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := H.h4 y hy
      refine ⟨fun i => ⟨x i, hx i⟩, ?_⟩
      apply Subtype.ext
      simp [f, Φt_apply]
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]
  simp

end Block

end PI.Dv.TIW
end
end
