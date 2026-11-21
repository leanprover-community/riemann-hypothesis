import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K1V
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K2V
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SingleSmulFin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SchmidCas

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Wt

theorem partialSum_finset_sum_eq {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) (k : ℕ) :
    kirrPs k (∑ i ∈ s, f i) = ∑ i ∈ s, kirrPs k (f i) := by
  simp only [kirrPs, Finset.sum_apply]
  exact Finset.sum_comm

theorem rootCone_entry_int (k : ℕ) (μ ν : Fin n → ℝ) : kirrPs k (μ + ν) = kirrPs k μ + kirrPs k ν := by
  simp only [kirrPs, Pi.add_apply, Finset.sum_add_distrib]

theorem partialSum_sub (k : ℕ) (μ ν : Fin n → ℝ) : kirrPs k (μ - ν) = kirrPs k μ - kirrPs k ν := by
  simp only [kirrPs, Pi.sub_apply, Finset.sum_sub_distrib]

theorem partialSum_smul (k : ℕ) (c : ℝ) (μ : Fin n → ℝ) : kirrPs k (c • μ) = c * kirrPs k μ := by
  simp only [kirrPs, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem partialSum_single (k : ℕ) (a : Fin n) :
    kirrPs k (Pi.single a (1 : ℝ)) = if a.val < k then 1 else 0 := by
  simp only [kirrPs, Finset.sum_pi_single', Finset.mem_filter, Finset.mem_univ, true_and]

theorem highestWeightVector_lift (k : ℕ) (a : Fin n) :
    0 ≤ kirrPs k (Pi.single a (1 : ℝ)) ∧ kirrPs k (Pi.single a (1 : ℝ)) ≤ 1 := by
  rw [partialSum_single]
  split_ifs <;> norm_num

theorem partialSum_root_nonneg {a b : Fin n} (hab : a < b) (k : ℕ) : 0 ≤ kirrPs k (root a b) := by
  have hv : a.val < b.val := hab
  rw [show root a b = Pi.single a (1 : ℝ) - Pi.single b 1 from rfl, partialSum_sub, partialSum_single, partialSum_single]
  split_ifs with h1 h2 h2
  · norm_num
  · norm_num
  · exfalso; omega
  · norm_num

theorem partialSum_single_bounds {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : 0 ≤ kirrPs k β := by
  obtain ⟨m, rfl⟩ := hβ
  rw [partialSum_finset_sum_eq]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [partialSum_finset_sum_eq]
  refine Finset.sum_nonneg fun b _ => ?_
  split_ifs with h
  · rw [partialSum_smul]
    exact mul_nonneg (Nat.cast_nonneg _) (partialSum_root_nonneg h k)
  · simp [kirrPs]

theorem partialSum_add_eq {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    kUnitWtLin (∑ i ∈ s, f i) = ∑ i ∈ s, kUnitWtLin (f i) := by
  simp only [kUnitWtLin, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem unitWeightSum_sub (μ ν : Fin n → ℝ) : kUnitWtLin (μ - ν) = kUnitWtLin μ - kUnitWtLin ν := by
  simp only [kUnitWtLin, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem unitWeightSum_smul (c : ℝ) (μ : Fin n → ℝ) : kUnitWtLin (c • μ) = c * kUnitWtLin μ := by
  simp only [kUnitWtLin, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem unitWeightSum_finset_sum {a b : Fin n} (hab : a < b) :
    kUnitWtLin (root a b) = (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) := by
  have hv : (a : ℕ) ≤ (b : ℕ) := le_of_lt (show (a : ℕ) < b from hab)
  rw [show root a b = Pi.single a (1 : ℝ) - Pi.single b 1 from rfl, unitWeightSum_sub, Nat.cast_sub hv]
  simp only [kUnitWtLin, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem tensorAction_ofLp {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, kUnitWtLin β = N := by
  obtain ⟨m, rfl⟩ := hβ
  refine ⟨∑ a, ∑ b, if a < b then m a b * ((b : ℕ) - (a : ℕ)) else 0, ?_⟩
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  rw [partialSum_add_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [partialSum_add_eq]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [unitWeightSum_smul, unitWeightSum_finset_sum h]
  · simp [kUnitWtLin]

theorem rootCone_unitWeightSum_nat {β : Fin n → ℝ} (hβ : InRootCone β) (c : Fin n) : ∃ z : ℤ, β c = z := by
  obtain ⟨m, rfl⟩ := hβ
  refine ⟨∑ a, ∑ b, if a < b then (m a b : ℤ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) else 0, ?_⟩
  simp only [Finset.sum_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a < b
  · simp only [h, if_true, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_sub,
      apply_ite (Int.cast : ℤ → ℝ), Int.cast_one, Int.cast_zero, root, Pi.sub_apply, Pi.single_apply]
  · simp only [h, if_false, Pi.zero_apply, Int.cast_zero]

theorem unitWeightSum_root (μ : Fin n → ℝ) (a : Fin n) : kirrPs (a.val + 1) μ = μ a + kirrPs a.val μ := by
  unfold kirrPs
  have hs : (univ.filter fun x : Fin n => x.val < a.val + 1) =
      Finset.cons a (univ.filter fun x : Fin n => x.val < a.val) (by simp) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons, Fin.ext_iff]
    omega
  rw [hs, Finset.sum_cons]

theorem aux_statement_19 {β : Fin n → ℝ} (h0 : ∀ k, 0 ≤ kirrPs k β) (h1 : ∀ k, kirrPs k β ≤ 1)
    (a : Fin n) : -1 ≤ β a ∧ β a ≤ 1 := by
  have h := unitWeightSum_root β a
  have h2 := h0 (a.val + 1)
  have h3 := h1 (a.val + 1)
  have h4 := h0 a.val
  have h5 := h1 a.val
  constructor <;> linarith

end Wt

section Dom

theorem highestWeight_dominant {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] {ε : Fin n → Bool}
    {A : Fin n → Fin n → Module.End ℂ N} (hA : IsGlRep A) (hU : IsKUnitary ε A) {ν : Fin n → ℝ}
    {y : N} (hy0 : y ≠ 0) (hy : IsKHWVec ε A ν y) {a b : Fin n} (hab : a < b) (hε : ε a = ε b) :
    ν b ≤ ν a := by
  have h0 : A a b y = 0 := hy.2 a b hab hε
  have hc : A a b (A b a y) = ((ν a - ν b : ℝ) : ℂ) • y := by
    have h := LinearMap.congr_fun (hA a b b a) y
    simp only [LinearMap.sub_apply, Module.End.mul_apply, h0, map_zero, sub_zero, if_true, hy.1] at h
    rw [h, Complex.ofReal_sub, sub_smul]
  have key : inner ℂ (A a b (A b a y)) y = inner ℂ (A b a y) (A b a y) := hU a b hε _ _
  rw [hc, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal] at key
  have key' : (ν a - ν b) * ‖y‖ ^ 2 = ‖A b a y‖ ^ 2 := by
    norm_cast at key
    first
    | exact Complex.ofReal_injective key
    | exact RCLike.ofReal_injective key
    | exact (Complex.ofReal_injective (by simpa using key))
  have hpos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
  by_contra hlt
  push_neg at hlt
  have := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos
  nlinarith [sq_nonneg ‖A b a y‖]

theorem rho_adjacent_same_sign {ε : Fin n → Bool} {a b : Fin n} (hab : a.val + 1 = b.val) (hε : ε a = ε b) :
    rhoC ε a - rhoC ε b = 1 ∧ rhoN ε a = rhoN ε b := by
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have e1 : (univ.filter fun c => a < c ∧ ε c = ε a) =
      Finset.cons b (univ.filter fun c => b < c ∧ ε c = ε b) (by simp) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hc : c = b
      · exact Or.inl hc
      · have hne : c.val ≠ b.val := fun h => hc (Fin.ext h)
        refine Or.inr ⟨?_, h2.trans hε⟩
        rw [Fin.lt_def] at h1 ⊢
        omega
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨hab', hε.symm⟩
      · exact ⟨hab'.trans h1, h2.trans hε.symm⟩
  have e2 : (univ.filter fun c => c < b ∧ ε c = ε b) =
      Finset.cons a (univ.filter fun c => c < a ∧ ε c = ε a) (by simp) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hc : c = a
      · exact Or.inl hc
      · have hne : c.val ≠ a.val := fun h => hc (Fin.ext h)
        refine Or.inr ⟨?_, h2.trans hε.symm⟩
        rw [Fin.lt_def] at h1 ⊢
        omega
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨hab', hε⟩
      · exact ⟨h1.trans hab', h2.trans hε⟩
  have e3 : (univ.filter fun c => a < c ∧ ε c ≠ ε a) = (univ.filter fun c => b < c ∧ ε c ≠ ε b) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have hc : c ≠ b := by rintro rfl; exact h2 hε.symm
      have hne : c.val ≠ b.val := fun h => hc (Fin.ext h)
      refine ⟨?_, fun h => h2 (h.trans hε.symm)⟩
      rw [Fin.lt_def] at h1 ⊢
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨hab'.trans h1, fun h => h2 (h.trans hε)⟩
  have e4 : (univ.filter fun c => c < b ∧ ε c ≠ ε b) = (univ.filter fun c => c < a ∧ ε c ≠ ε a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have hc : c ≠ a := by rintro rfl; exact h2 hε
      have hne : c.val ≠ a.val := fun h => hc (Fin.ext h)
      refine ⟨?_, fun h => h2 (h.trans hε)⟩
      rw [Fin.lt_def] at h1 ⊢
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans hab', fun h => h2 (h.trans hε.symm)⟩
  refine ⟨?_, ?_⟩
  · simp only [rhoC]
    rw [e1, e2, Finset.card_cons, Finset.card_cons]
    push_cast
    ring
  · simp only [rhoN]
    rw [e3, e4]

end Dom

section Irr

theorem exists_minimal_kStable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
    {A : Fin n → Fin n → Module.End ℂ X} {S : Submodule ℂ X} (hfd : FiniteDimensional ℂ S)
    (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ W ≤ S, W ≠ ⊥ ∧ IsKStableSub ε A W ∧
      ∀ W' : Submodule ℂ X, W' ≤ W → IsKStableSub ε A W' → W' = ⊥ ∨ W' = W := by
  classical
  have hex : ∃ d, ∃ W : Submodule ℂ X, W ≤ S ∧ W ≠ ⊥ ∧ IsKStableSub ε A W ∧ Module.finrank ℂ W = d :=
    ⟨_, S, le_rfl, hne, hS, rfl⟩
  obtain ⟨W, hWS, hW0, hWst, hWd⟩ := Nat.find_spec hex
  refine ⟨W, hWS, hW0, hWst, fun W' hW'W hW'st => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hlt : W' < W := lt_of_le_of_ne hW'W h2
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  have hr := Submodule.finrank_lt_finrank_of_lt hlt
  exact Nat.find_min hex (by rw [← hWd]; exact hr) ⟨W', hW'W.trans hWS, h1, hW'st, rfl⟩

private theorem k3a_joint_lemma {N : Type*} [AddCommGroup N] [Module ℂ N] (T : Fin n → Module.End ℂ N)
    (hc : ∀ i j x, T i (T j x) = T j (T i x)) (s : Finset (Fin n)) :
    ∀ U : Submodule ℂ N, FiniteDimensional ℂ U → (∀ i, ∀ u ∈ U, T i u ∈ U) → U ≠ ⊥ →
      ∃ u ∈ U, u ≠ 0 ∧ ∀ i ∈ s, ∃ l : ℂ, T i u = l • u := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro U _ _ hne
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨u, hu, hu0, fun i hi => by simp at hi⟩
  · intro j s _ ih U hfd hst hne
    haveI := hfd
    haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((T j).restrict (hst j))
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hl
    obtain ⟨hvm, hvne⟩ := Module.End.hasEigenvector_iff.mp hv
    have hv1 := Module.End.mem_eigenspace_iff.mp hvm
    have hTv : T j (v : N) = l • (v : N) := by
      have h := congrArg Subtype.val hv1
      simpa [LinearMap.restrict_apply] using h
    have hv0 : (v : N) ≠ 0 := fun h => hvne (Subtype.ext h)
    have memU : ∀ x, x ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) ↔ x ∈ U ∧ T j x = l • x := by
      intro x
      simp [Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hUne : U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) ≠ ⊥ := by
      intro h
      have hm : (v : N) ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) := (memU _).mpr ⟨v.2, hTv⟩
      rw [h, Submodule.mem_bot] at hm
      exact hv0 hm
    have hUst : ∀ i, ∀ u ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)),
        T i u ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) := by
      intro i u hu
      rw [memU] at hu ⊢
      refine ⟨hst i u hu.1, ?_⟩
      rw [hc j i, hu.2, map_smul]
    haveI : FiniteDimensional ℂ (U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) : Submodule ℂ N) :=
      Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨u, hu, hu0, hall⟩ := ih _ inferInstance hUst hUne
    rw [memU] at hu
    refine ⟨u, hu.1, hu0, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨l, hu.2⟩
    · exact hall i hi

theorem exists_kIrreducible_highestWeight {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ N} (hA : IsGlRep A) (hU : IsKUnitary ε A)
    {S : Submodule ℂ N} (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ W ≤ S, ∃ ν : Fin n → ℝ, IsKIrrHW ε A ν W := by
  classical
  obtain ⟨W, hWS, hW0, hWst, hWmin⟩ := exists_minimal_kStable hfd hS hne
  haveI hWfd : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨H, hH⟩ : ∃ H : Module.End ℂ N, ∀ x, H x = ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • A c c x :=
    ⟨∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • A c c, fun x => by simp⟩
  have hcomm1 : ∀ a b c x, A c c (A a b x) - A a b (A c c x) =
      (if c = a then A a b x else 0) - (if c = b then A a b x else 0) := by
    intro a b c x
    have h := LinearMap.congr_fun (hA c c a b) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [h]
    by_cases h1 : c = a <;> by_cases h2 : c = b
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have hHr : ∀ a b x, H (A a b x) = A a b (H x) + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ)) • A a b x := by
    intro a b x
    rw [← sub_eq_iff_eq_add', hH, hH, map_sum, ← Finset.sum_sub_distrib]
    simp only [map_smul, ← smul_sub, hcomm1]
    simp only [smul_sub, smul_ite, smul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← sub_smul]
    congr 1
    ring
  have hcomm : ∀ i j x, A i i (A j j x) = A j j (A i i x) := by
    intro i j x
    have h := hcomm1 j j i x
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hHW : ∀ x ∈ W, H x ∈ W := by
    intro x hx
    rw [hH]
    exact W.sum_mem fun c _ => W.smul_mem _ (hWst c c rfl x hx)
  have hfin := Module.End.finite_hasEigenvalue (H.restrict hHW)
  obtain ⟨μ0, hμ0⟩ := Module.End.exists_eigenvalue (H.restrict hHW)
  obtain ⟨μ, hμ, hmax⟩ := Set.exists_max_image _ (fun z : ℂ => z.re) hfin ⟨μ0, hμ0⟩
  have hbound : ∀ y ∈ W, y ≠ 0 → ∀ z : ℂ, H y = z • y → z.re ≤ μ.re := by
    intro y hy hy0 z hz
    refine hmax z ?_
    show Module.End.HasEigenvalue (H.restrict hHW) z
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨y, hy⟩) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, ?_⟩
    · ext
      simp [LinearMap.restrict_apply, hz]
    · intro h
      apply hy0
      simpa using congrArg Subtype.val h
  have hkill : ∀ u, u ∈ W → H u = μ • u → ∀ a b, a < b → ε a = ε b → A a b u = 0 := by
    intro u huW hHu a b hab he
    by_contra hne'
    have h1 : H (A a b u) = (μ + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ))) • A a b u := by
      rw [hHr a b u, hHu, map_smul, add_smul]
    have h2 := hbound _ (hWst a b he u huW) hne' _ h1
    have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) < b from hab)
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re] at h2
    linarith
  obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
  obtain ⟨hvm, hvne⟩ := Module.End.hasEigenvector_iff.mp hv
  have hv1 := Module.End.mem_eigenspace_iff.mp hvm
  have hHv : H (v : N) = μ • (v : N) := by
    have h := congrArg Subtype.val hv1
    simpa [LinearMap.restrict_apply] using h
  have hv0 : (v : N) ≠ 0 := fun h => hvne (Subtype.ext h)
  have memU : ∀ x, x ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) ↔ x ∈ W ∧ H x = μ • x := by
    intro x
    simp [Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
  have hUne : W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) ≠ ⊥ := by
    intro h
    have hm : (v : N) ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) := (memU _).mpr ⟨v.2, hHv⟩
    rw [h, Submodule.mem_bot] at hm
    exact hv0 hm
  have hUst : ∀ c, ∀ u ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)),
      A c c u ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) := by
    intro c u hu
    rw [memU] at hu ⊢
    refine ⟨hWst c c rfl u hu.1, ?_⟩
    rw [hHr c c u, hu.2, map_smul, sub_self, zero_smul, add_zero]
  haveI : FiniteDimensional ℂ (W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) : Submodule ℂ N) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨u, hu, hu0, hall⟩ := k3a_joint_lemma (fun c => A c c) hcomm univ _ inferInstance hUst hUne
  rw [memU] at hu
  choose l hl using fun c => hall c (Finset.mem_univ c)
  have hl' : ∀ c, A c c u = l c • u := fun c => hl c
  have hreal : ∀ c, (((l c).re : ℝ) : ℂ) = l c := by
    intro c
    have h1 := hU c c rfl u u
    rw [hl' c, inner_smul_left, inner_smul_right] at h1
    have hne2 : inner ℂ u u ≠ 0 := inner_self_ne_zero.mpr hu0
    exact Complex.conj_eq_iff_re.mp (mul_right_cancel₀ hne2 h1)
  refine ⟨W, hWS, fun c => (l c).re, hWfd, hWst, hWmin, u, hu.1, hu0, fun a => ?_,
    fun a b hab he => hkill u hu.1 hu.2 a b hab he⟩
  rw [hreal a]
  exact hl' a

end Irr

section Lift

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem entry_bounds_of_partialSum {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, h] <;> rfl

def k3aT (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) :
    Module.End ℂ (PiLp 2 fun _ : Fin n => D) :=
  if ε a = ε b then
    (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap ∘ₗ tensV E a b ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Fin n → D)).toLinearMap
  else 0

theorem tensorAction_apply_eq {a b : Fin n} (hab : ε a = ε b) (x : PiLp 2 fun _ : Fin n => D) :
    WithLp.ofLp (k3aT ε E a b x) = tensV E a b (WithLp.ofLp x) := by
  rw [k3aT, if_pos hab]
  rfl

theorem partialSum_nonneg_rootCone (hU : IsKUnitary ε E) : IsKUnitary ε (k3aT ε E) := by
  intro a b hab x y
  have e1 : ∀ c, WithLp.ofLp (k3aT ε E a b x) c = E a b (WithLp.ofLp x c) + (if c = a then WithLp.ofLp x b else 0) :=
    fun c => by rw [tensorAction_apply_eq hab, entry_bounds_of_partialSum]
  have e2 : ∀ c, WithLp.ofLp (k3aT ε E b a y) c = E b a (WithLp.ofLp y c) + (if c = b then WithLp.ofLp y a else 0) :=
    fun c => by rw [tensorAction_apply_eq hab.symm, entry_bounds_of_partialSum]
  have l : ∀ c, inner ℂ (if c = a then WithLp.ofLp x b else 0) (WithLp.ofLp y c) =
      if c = a then inner ℂ (WithLp.ofLp x b) (WithLp.ofLp y a) else 0 := by
    intro c
    split_ifs with h
    · subst h; rfl
    · exact inner_zero_left _
  have r : ∀ c, inner ℂ (WithLp.ofLp x c) (if c = b then WithLp.ofLp y a else 0) =
      if c = b then inner ℂ (WithLp.ofLp x b) (WithLp.ofLp y a) else 0 := by
    intro c
    split_ifs with h
    · subst h; rfl
    · exact inner_zero_right _
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [e1, e2, inner_add_left, inner_add_right, Finset.sum_add_distrib, l, r, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_congr rfl fun c _ => hU a b hab (WithLp.ofLp x c) (WithLp.ofLp y c)]

end Lift

section Lift2

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem partialSum_succ_alt (hU : IsKUnitary ε E) {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {B : Fin n → Fin n → Module.End ℂ Y} (g : (Fin n → D) →ₗ[ℂ] Y) {S : Submodule ℂ (Fin n → D)}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε (tensV E) S)
    (hg : ∀ a b, ε a = ε b → ∀ x ∈ S, g (tensV E a b x) = B a b (g x))
    {x₀ : Fin n → D} (hx₀ : x₀ ∈ S) {μ : Fin n → ℝ} (hy : IsKHWVec ε B μ (g x₀)) :
    ∃ x ∈ S, IsKHWVec ε (tensV E) μ x ∧ g x = g x₀ := by
  classical
  have hTe : ∀ a b, ε a = ε b → ∀ v : Fin n → D, k3aT ε E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)).symm v) = (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a b v) := by
    intro a b hab v
    apply (WithLp.linearEquiv 2 ℂ (Fin n → D)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact tensorAction_apply_eq hab _
  haveI hKfd : FiniteDimensional ℂ (S ⊓ LinearMap.ker g : Submodule ℂ (Fin n → D)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℂ (WithLp 2 (Fin n → D)),
      K = (S ⊓ LinearMap.ker g).map ((WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ K := by rw [hK]; infer_instance
  have hmemK : ∀ v, v ∈ S → g v = 0 → (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm v ∈ K := by
    intro v hv hfv
    rw [hK]
    exact Submodule.mem_map_of_mem (Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr hfv⟩)
  have hKmem : ∀ u ∈ K, (WithLp.linearEquiv 2 ℂ (Fin n → D)) u ∈ S ∧ g ((WithLp.linearEquiv 2 ℂ (Fin n → D)) u) = 0 := by
    intro u hu
    rw [hK] at hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    have hv' := Submodule.mem_inf.mp hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact ⟨hv'.1, LinearMap.mem_ker.mp hv'.2⟩
  have hKst : ∀ a b, ε a = ε b → ∀ u ∈ K, k3aT ε E a b u ∈ K := by
    intro a b hab u hu
    obtain ⟨h1, h2⟩ := hKmem u hu
    have e1 : k3aT ε E a b u = (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) u)) := by
      rw [← hTe a b hab, LinearEquiv.symm_apply_apply]
    rw [e1]
    exact hmemK _ (hS a b hab _ h1) (by rw [hg a b hab _ h1, h2, map_zero])
  have hUT := partialSum_nonneg_rootCone hU
  have hperp : ∀ a b, ε a = ε b → ∀ v ∈ Kᗮ, k3aT ε E a b v ∈ Kᗮ := by
    intro a b hab v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← hUT b a hab.symm u v]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hKst b a hab.symm u hu)
  obtain ⟨k, hk, c, hc, hkc⟩ := K.exists_add_mem_mem_orthogonal ((WithLp.linearEquiv 2 ℂ (Fin n → D)).symm x₀)
  obtain ⟨hkS, hkf⟩ := hKmem k hk
  have hx : (WithLp.linearEquiv 2 ℂ (Fin n → D)) c = x₀ - (WithLp.linearEquiv 2 ℂ (Fin n → D)) k := by
    have h3 := congrArg (WithLp.linearEquiv 2 ℂ (Fin n → D)) hkc
    rw [LinearEquiv.apply_symm_apply, map_add] at h3
    rw [h3]
    abel
  have hxS : (WithLp.linearEquiv 2 ℂ (Fin n → D)) c ∈ S := by
    rw [hx]
    exact S.sub_mem hx₀ hkS
  have hfx : g ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) = g x₀ := by rw [hx, map_sub, hkf, sub_zero]
  have hzero : ∀ w, w ∈ S → g w = 0 → (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm w ∈ Kᗮ → w = 0 := by
    intro w hw hfw hpw
    have hm : (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm w ∈ K ⊓ Kᗮ := Submodule.mem_inf.mpr ⟨hmemK w hw hfw, hpw⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.injective (hm.trans (map_zero _).symm)
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin n → D)) c, hxS, ⟨fun a => ?_, fun a b hab he => ?_⟩, hfx⟩
  · have hw : tensV E a a ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) - (μ a : ℂ) • (WithLp.linearEquiv 2 ℂ (Fin n → D)) c ∈ S := S.sub_mem (hS a a rfl _ hxS) (S.smul_mem _ hxS)
    have hfw : g (tensV E a a ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) - (μ a : ℂ) • (WithLp.linearEquiv 2 ℂ (Fin n → D)) c) = 0 := by
      rw [map_sub, map_smul, hg a a rfl _ hxS, hfx, hy.1 a, sub_self]
    have hp : (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a a ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) - (μ a : ℂ) • (WithLp.linearEquiv 2 ℂ (Fin n → D)) c) ∈ Kᗮ := by
      rw [map_sub, map_smul, ← hTe a a rfl, LinearEquiv.symm_apply_apply]
      exact Kᗮ.sub_mem (hperp a a rfl c hc) (Kᗮ.smul_mem _ hc)
    exact sub_eq_zero.mp (hzero _ hw hfw hp)
  · have hw : tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) ∈ S := hS a b he _ hxS
    have hfw : g (tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c)) = 0 := by rw [hg a b he _ hxS, hfx, hy.2 a b hab he]
    have hp : (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c)) ∈ Kᗮ := by
      rw [← hTe a b he, LinearEquiv.symm_apply_apply]
      exact hperp a b he c hc
    exact hzero _ hw hfw hp

end Lift2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Gen

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {V : Submodule ℂ M}

theorem generatedSubmodule_stable (a b : Fin n) {v : M} (hv : v ∈ genSub E V) : E a b v ∈ genSub E V := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem le_generatedSubmodule : V ≤ genSub E V := le_sInf fun _ hT => hT.1

theorem eulerAction_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem tensorAction_mem_generated {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) (a b : Fin n) :
    ∀ c, tensV E a b f c ∈ genSub E V := by
  intro c
  rw [entry_bounds_of_partialSum]
  refine Submodule.add_mem _ (generatedSubmodule_stable a b (hf c)) ?_
  split_ifs
  · exact hf b
  · exact Submodule.zero_mem _

theorem eulerAction_mem_generated {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) : ∀ d, eeV E f d ∈ genSub E V := by
  intro d
  rw [eulerAction_apply]
  exact Submodule.sum_mem _ fun c _ => generatedSubmodule_stable c d (hf c)

theorem tensorAction_comm_euler (hE : IsGlRep E) (a b : Fin n) (f : Fin n → M) :
    tensV E a b (eeV E f) = eeV E (tensV E a b f) := by
  have key : ∀ c d, E a b (E d c (f d)) = E d c (E a b (f d)) +
      ((if b = d then E a c (f d) else 0) - (if c = a then E d b (f d) else 0)) := by
    intro c d
    have h := LinearMap.congr_fun (hE a b d c) (f d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply,
      apply_ite (fun T : Module.End ℂ M => T (f d)), LinearMap.zero_apply] at h
    rw [← h]; abel
  funext c
  rw [entry_bounds_of_partialSum, eulerAction_apply, eulerAction_apply, eulerAction_apply, map_sum]
  simp only [entry_bounds_of_partialSum, map_add, key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ d, (if b = d then E a c (f d) else 0) = E a c (f b) := by simp
  have e2 : ∑ d, E d c (if d = a then f b else 0) = E a c (f b) := by simp [apply_ite]
  rw [e1, e2]
  by_cases hca : c = a
  · subst hca; simp; abel
  · simp [hca]

theorem finiteDimensional_pi_submodule (hV : FiniteDimensional ℂ V) :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => V) := by
  let F : (Fin n → V) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun i => V.subtype ∘ₗ LinearMap.proj i
  have : Submodule.pi Set.univ (fun _ : Fin n => V) ≤ LinearMap.range F := by
    intro f hf
    exact ⟨fun i => ⟨f i, hf i (Set.mem_univ i)⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le this

end Gen

section Poly

variable {X' : Type*} [AddCommGroup X'] [Module ℂ X']

theorem aeval_induction (A : Module.End ℂ X') (P : Module.End ℂ X' → Prop) (h1 : ∀ a : ℂ, P (a • 1))
    (hadd : ∀ S T, P S → P T → P (S + T)) (hmul : ∀ S, P S → P (S * A)) (p : ℂ[X]) :
    P (aeval A p) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C, Algebra.algebraMap_eq_smul_one]; exact h1 a
  | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact hmul _ h

theorem aeval_mul_commute {A B : Module.End ℂ X'} (h : A * B = B * A) (p : ℂ[X]) :
    aeval A p * B = B * aeval A p := by
  refine aeval_induction A (fun S => S * B = B * S) ?_ ?_ ?_ p
  · intro a; rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  · intro S T hS hT; rw [add_mul, mul_add, hS, hT]
  · intro S hS; rw [mul_assoc, h, ← mul_assoc, hS, mul_assoc]

theorem aeval_mem_of_stable_alt {A : Module.End ℂ X'} {G : Submodule ℂ X'} (hG : ∀ x ∈ G, A x ∈ G) (p : ℂ[X]) :
    ∀ x ∈ G, aeval A p x ∈ G := by
  refine aeval_induction A (fun S => ∀ x ∈ G, S x ∈ G) ?_ ?_ ?_ p
  · intro a x hx; exact G.smul_mem a hx
  · intro S T hS hT x hx; exact G.add_mem (hS x hx) (hT x hx)
  · intro S hS x hx; exact hS _ (hG x hx)

theorem prodShift_eq_aeval_prod (A : Module.End ℂ X') (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  rw [prodShift, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun t => ?_)
  simp [Algebra.algebraMap_eq_smul_one]

end Poly

section Xs

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {V : Submodule ℂ M}

def k3bP (θ : Fin n → ℝ) (s : Fin n) : ℂ[X] := ∏ t ∈ univ.erase s, (X - C ((θ t : ℝ) : ℂ))

theorem mem_eigenTensorSpace_gen_iff {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs (eeV E) (genSub E V) θ ↔ (∀ c, f c ∈ genSub E V) ∧ eeV E f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_pi, sub_eq_zero]

theorem lagrange_mem_generated (p : ℂ[X]) {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) :
    ∀ c, aeval (eeV E) p f c ∈ genSub E V := by
  have := aeval_mem_of_stable_alt (A := eeV E) (G := Submodule.pi Set.univ fun _ => genSub E V)
    (fun x hx => fun c _ => eulerAction_mem_generated (fun c => hx c (Set.mem_univ c)) c) p f (fun c _ => hf c)
  exact fun c => this c (Set.mem_univ c)

theorem lagrange_mem_eigenTensorSpace {θ : Fin n → ℝ}
    (hK1 : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → prodShift (eeV E) θ f = 0) (s : Fin n)
    {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) :
    aeval (eeV E) (k3bP θ s) f ∈ Xs (eeV E) (genSub E V) (θ s) := by
  rw [mem_eigenTensorSpace_gen_iff]
  refine ⟨lagrange_mem_generated _ hf, ?_⟩
  have h := hK1 f hf
  rw [prodShift_eq_aeval_prod, ← Finset.mul_prod_erase univ (fun t => X - C ((θ t : ℝ) : ℂ)) (mem_univ s),
    map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

theorem lagrange_on_eigenTensorSpace (θ : Fin n → ℝ) (s : Fin n) {x : Fin n → M}
    (hx : x ∈ Xs (eeV E) (genSub E V) (θ s)) :
    aeval (eeV E) (k3bP θ s) x = (k3bP θ s).eval ((θ s : ℝ) : ℂ) • x :=
  Module.End.aeval_apply_of_mem_apply_eq_smul (mem_eigenTensorSpace_gen_iff.1 hx).2

theorem lagrangeFactor_eval_ne_zero_of_injective {θ : Fin n → ℝ} (hθ : Function.Injective θ) (s : Fin n) :
    (k3bP θ s).eval ((θ s : ℝ) : ℂ) ≠ 0 := by
  rw [k3bP, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro t ht
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact (Finset.ne_of_mem_erase ht) (hθ (Complex.ofReal_injective h)).symm

theorem aeval_tensorAction_comm (hE : IsGlRep E) (p : ℂ[X]) (a b : Fin n) (f : Fin n → M) :
    aeval (eeV E) p (tensV E a b f) = tensV E a b (aeval (eeV E) p f) := by
  have h : eeV E * tensV E a b = tensV E a b * eeV E := by
    refine LinearMap.ext fun g => ?_
    exact (tensorAction_comm_euler hE a b g).symm
  exact LinearMap.congr_fun (aeval_mul_commute h p) f

theorem eigenTensorSpace_stable (hE : IsGlRep E) (a b : Fin n) {θ : ℝ} {f : Fin n → M}
    (hf : f ∈ Xs (eeV E) (genSub E V) θ) : tensV E a b f ∈ Xs (eeV E) (genSub E V) θ := by
  rw [mem_eigenTensorSpace_gen_iff] at hf ⊢
  refine ⟨tensorAction_mem_generated hf.1 a b, ?_⟩
  rw [← tensorAction_comm_euler hE, hf.2, map_smul]

theorem generated_eigenspace_annihilate {N : Type*} [AddCommGroup N] [Module ℂ N] (EN : Fin n → Fin n → Module.End ℂ N)
    (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensV E a b f) = EN a b (φ f))
    (T : Module.End ℂ (Fin n → M)) (hT : ∀ a b f, T (tensV E a b f) = tensV E a b (T f))
    (hTG : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → ∀ c, T f c ∈ genSub E V)
    (hz : ∀ u : Fin n → M, (∀ c, u c ∈ V) → φ (T u) = 0) {f : Fin n → M}
    (hf : f ∈ genSub (tensV E) (Submodule.pi Set.univ fun _ => V)) : φ (T f) = 0 := by
  let Z : Submodule ℂ (Fin n → M) :=
    Submodule.pi Set.univ (fun _ => genSub E V) ⊓ LinearMap.ker (φ ∘ₗ T)
  have hZ : ∀ g, g ∈ Z ↔ (∀ c, g c ∈ genSub E V) ∧ φ (T g) = 0 := fun g => by
    simp [Z, Submodule.mem_pi]
  have hle : genSub (tensV E) (Submodule.pi Set.univ fun _ => V) ≤ Z := by
    refine sInf_le ⟨fun u hu => (hZ u).2 ⟨fun c => le_generatedSubmodule (hu c (Set.mem_univ c)),
      hz u fun c => hu c (Set.mem_univ c)⟩, ?_⟩
    intro a b g hg
    rw [hZ] at hg ⊢
    refine ⟨tensorAction_mem_generated hg.1 a b, ?_⟩
    rw [hT, hφ a b _ (hTG g hg.1), hg.2, map_zero]
  exact ((hZ f).1 (hle hf)).2

theorem casimir_map_intertwiner {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensV E a b f) = EN a b (φ f))
    {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) : casimir EN (φ f) = φ (casimir (tensV E) f) := by
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hφ a b _ (tensorAction_mem_generated hf b a), hφ b a _ hf]

end Xs

theorem casimirValue_add_single (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam + Pi.single s 1) = casVal lam + n + 2 * thV lam s := by
  simp only [casVal, nsq, dot, thV, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem lowestKType_add_single (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) :
    lowK ε (lam + Pi.single s 1) = lowK ε lam + Pi.single s 1 := by
  unfold lowK; abel

theorem lowestKType_shift_inv (ε : Fin n → Bool) (ν : Fin n → ℝ) : lowK ε (ν + rhoC ε - rhoN ε) = ν := by
  unfold lowK; abel

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem strictAnti_of_adjacent {f : Fin n → ℝ} (h : ∀ a b : Fin n, a.val + 1 = b.val → f b < f a) :
    StrictAnti f := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m => exact Fin.strictAnti_iff_succ_lt.2 fun i => h _ _ (by simp)

theorem sub_le_abs_add {h c x y : ℝ} (hx : h ≤ |x|) (hy1 : -c ≤ y) (hy2 : y ≤ c) : h - c ≤ |x + y| := by
  have h1 := abs_sub_abs_le_abs_sub x (-y)
  rw [sub_neg_eq_add, abs_neg] at h1
  have h2 : |y| ≤ c := abs_le.2 ⟨hy1, hy2⟩
  linarith

theorem single_entry_int (s a : Fin n) : ∃ z : ℤ, (Pi.single s 1 : Fin n → ℝ) a = z := by
  rw [Pi.single_apply]; split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem three_add_le_gapBound (ε : Fin n → Bool) : 3 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ hNeed ε := by
  have h1 := le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
  have h2 : 2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε :=
    le_max_left _ _
  linarith

theorem shifted_weight_parameter {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} {s c0 : Fin n} {ν : Fin n → ℝ}
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hGL : GapLap ε lam h)
    (hcone : InRootCone (ν - lowK ε (lam + Pi.single s 1)))
    (hbd : ∀ k, kirrPs k ν ≤ kirrPs k (lowK ε lam + Pi.single c0 1))
    (hdom : ∀ a b : Fin n, a < b → ε a = ε b → ν b ≤ ν a) :
    (∀ a, ∃ m : ℤ, (ν + rhoC ε - rhoN ε) a - ((n : ℝ) - 1) / 2 = (m : ℝ)) ∧
      StrictAnti (ν + rhoC ε - rhoN ε) ∧ GapAtLeast ε (ν + rhoC ε - rhoN ε) (h - 2) ∧
      hNeed ε < h - 2 + 2 ∧ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h - 2 ∧
      ν + rhoC ε - rhoN ε = (lam + Pi.single s 1) + (ν - lowK ε (lam + Pi.single s 1)) := by
  obtain ⟨hmono, hh, hN⟩ := hGL
  set γ := ν - lowK ε lam with hγ
  have hγβ : γ = Pi.single s 1 + (ν - lowK ε (lam + Pi.single s 1)) := by
    rw [hγ, lowestKType_add_single]; abel
  have heq' : ν + rhoC ε - rhoN ε = lam + γ := by rw [hγ]; unfold lowK; abel
  have heq : ν + rhoC ε - rhoN ε = (lam + Pi.single s 1) + (ν - lowK ε (lam + Pi.single s 1)) := by
    rw [heq', hγβ]; abel
  have hb0 : ∀ k, 0 ≤ kirrPs k γ := by
    intro k; rw [hγβ, rootCone_entry_int]
    linarith [(highestWeightVector_lift k s).1, partialSum_single_bounds hcone k]
  have hb1 : ∀ k, kirrPs k γ ≤ 1 := by
    intro k; rw [hγ, partialSum_sub]
    have := hbd k; rw [rootCone_entry_int] at this
    linarith [(highestWeightVector_lift k c0).2]
  have hent := aux_statement_19 hb0 hb1
  have hN1 := three_add_le_gapBound ε
  have hg0 : 0 ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by positivity
  refine ⟨fun a => ?_, ?_, ?_, by linarith, by linarith, heq⟩
  · obtain ⟨m, hm⟩ := hint a
    obtain ⟨z1, hz1⟩ := single_entry_int s a
    obtain ⟨z2, hz2⟩ := rootCone_unitWeightSum_nat hcone a
    refine ⟨m + z1 + z2, ?_⟩
    rw [heq', hγβ]
    simp only [Pi.add_apply]
    rw [hz1, hz2]
    push_cast
    linarith
  · refine strictAnti_of_adjacent fun a b hab => ?_
    have hlt : a < b := Fin.lt_def.2 (by omega)
    by_cases hε : ε a = ε b
    · obtain ⟨h1, h2⟩ := rho_adjacent_same_sign hab hε
      have := hdom a b hlt hε
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith
    · have hl := hmono hlt
      have hg := hh a b hε
      rw [abs_of_pos (by linarith)] at hg
      rw [heq']
      simp only [Pi.add_apply]
      linarith [(hent a).1, (hent b).2]
  · intro a b hε
    rw [heq']
    simp only [Pi.add_apply]
    have := sub_le_abs_add (hh a b hε) (y := γ a - γ b) (c := 2)
      (by linarith [(hent a).1, (hent b).2]) (by linarith [(hent a).2, (hent b).1])
    convert this using 2
    ring

theorem k3V (n : ℕ) : QuotientHighestWeightTensorStandard n := by
  intro ε lam h H _ _ _ σ D E V s N _ _ EN φ x hσ hD hV hc hVK hint hmono hGL hp hq hmono' hEN hUN
    hφ hx hφx
  classical
  have hE : IsGlRep E := hD.glRep
  have hKD : IsKUnitary ε E := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hKN : IsKUnitary ε EN := isKUnitary_of_isInfUnitary hUN
  have hK1 := k1V n ε lam h H σ D E V hσ hD hV hc hVK hint hmono hGL hp hq
  have hK2 := (k2V n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hGL hp hq).1
  have hgen := (gen_statement n ε D E V hE hV.2.1).1
  have hT := tens_statement n D E hE
  obtain ⟨X0, hX0⟩ : ∃ X0, X0 = Xs (eeV E) (genSub E V) (thV lam s) := ⟨_, rfl⟩
  have hX0mem : ∀ f, f ∈ X0 ↔ (∀ c, f c ∈ genSub E V) ∧ eeV E f = ((thV lam s : ℝ) : ℂ) • f := by
    intro f; rw [hX0]; exact mem_eigenTensorSpace_gen_iff
  have hX0st : ∀ a b f, f ∈ X0 → tensV E a b f ∈ X0 := by
    rw [hX0]; exact fun a b f hf => eigenTensorSpace_stable hE a b hf
  rw [← hX0] at hx hK2
  obtain ⟨P, hP⟩ : ∃ P : Module.End ℂ (Fin n → D), P = aeval (eeV E) (k3bP (thV lam) s) := ⟨_, rfl⟩
  have hPcomm : ∀ a b f, P (tensV E a b f) = tensV E a b (P f) := by
    rw [hP]; exact fun a b f => aeval_tensorAction_comm hE _ a b f
  have hPmem : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → ∀ c, P f c ∈ genSub E V := by
    rw [hP]; exact fun f hf => lagrange_mem_generated _ hf
  have hPX : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → P f ∈ X0 := by
    rw [hP, hX0]; exact fun f hf => lagrange_mem_eigenTensorSpace hK1 s hf
  have hPon : ∀ y ∈ X0, P y = (k3bP (thV lam) s).eval ((thV lam s : ℝ) : ℂ) • y := by
    rw [hP, hX0]; exact fun y hy => lagrange_on_eigenTensorSpace _ s hy
  have hθinj : Function.Injective (thV lam) := fun a b hab => hmono.injective (by unfold thV at hab; linarith)
  have hPne := lagrangeFactor_eval_ne_zero_of_injective hθinj s

  have hstart : ∃ u : Fin n → D, (∀ c, u c ∈ V) ∧ φ (P u) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h0 : φ (P x) = 0 := generated_eigenspace_annihilate EN φ hφ P hPcomm hPmem hne (hgen x ((hX0mem x).1 hx).1)
    rw [hPon x hx, map_smul] at h0
    exact hφx ((smul_eq_zero.1 h0).resolve_left hPne)
  obtain ⟨u0, hu0V, hu0φ⟩ := hstart
  obtain ⟨piV, hpiV⟩ : ∃ piV : Submodule ℂ (Fin n → D), piV = Submodule.pi Set.univ (fun _ => V) :=
    ⟨_, rfl⟩
  have hpiV_mem : ∀ u, u ∈ piV ↔ ∀ c, u c ∈ V := fun u => by rw [hpiV]; simp [Submodule.mem_pi]
  have hpiVfd : FiniteDimensional ℂ piV := by rw [hpiV]; exact finiteDimensional_pi_submodule hV.1
  have hpiVst : IsKStableSub ε (tensV E) piV := by
    intro a b hab u hu
    rw [hpiV_mem] at hu ⊢
    intro c
    rw [entry_bounds_of_partialSum]
    refine V.add_mem (hV.2.1 a b hab _ (hu c)) ?_
    split_ifs
    · exact hu b
    · exact V.zero_mem
  have hpiVG : ∀ u ∈ piV, ∀ c, u c ∈ genSub E V := fun u hu c => le_generatedSubmodule ((hpiV_mem u).1 hu c)
  have hS0fd : FiniteDimensional ℂ (piV.map P) := inferInstance
  have hS0X : piV.map P ≤ X0 := by rintro _ ⟨u, hu, rfl⟩; exact hPX u (hpiVG u hu)
  have hS0st : IsKStableSub ε (tensV E) (piV.map P) := by
    rintro a b hab _ ⟨u, hu, rfl⟩
    rw [← hPcomm]
    exact Submodule.mem_map_of_mem (hpiVst a b hab u hu)

  have himg : ∀ S : Submodule ℂ (Fin n → D), S ≤ X0 → IsKStableSub ε (tensV E) S →
      IsKStableSub ε EN (S.map φ) := by
    rintro S hSX hSst a b hab _ ⟨f, hf, rfl⟩
    rw [← hφ a b f ((hX0mem f).1 (hSX hf)).1]
    exact Submodule.mem_map_of_mem (hSst a b hab f hf)
  have hcone : ∀ S : Submodule ℂ (Fin n → D), FiniteDimensional ℂ S → S ≤ X0 →
      IsKStableSub ε (tensV E) S → ∀ (W : Submodule ℂ N) (ν : Fin n → ℝ), W ≤ S.map φ →
      IsKIrrHW ε EN ν W → InRootCone (ν - lowK ε (lam + Pi.single s 1)) := by
    intro S hfd hSX hSst W ν hWS hW
    obtain ⟨w, hwW, hw0, hwK⟩ := hW.2.2.2
    obtain ⟨f0, hf0, hf0eq⟩ := Submodule.mem_map.1 (hWS hwW)
    obtain ⟨f, hfS, hfK, hff⟩ := partialSum_succ_alt hKD φ hfd hSst
      (fun a b _ g hg => hφ a b g ((hX0mem g).1 (hSX hg)).1) hf0 (by rw [hf0eq]; exact hwK)
    refine hK2 ν f (hSX hfS) ?_ hfK
    rintro rfl
    rw [map_zero, hf0eq] at hff
    exact hw0 hff.symm

  have hS0ne : (piV.map P).map φ ≠ ⊥ := by
    intro h0
    have : φ (P u0) ∈ (piV.map P).map φ :=
      Submodule.mem_map_of_mem (Submodule.mem_map_of_mem ((hpiV_mem u0).2 hu0V))
    rw [h0, Submodule.mem_bot] at this
    exact hu0φ this
  obtain ⟨W1, hW1S, ν1, hW1⟩ := exists_kIrreducible_highestWeight hEN hKN inferInstance (himg _ hS0X hS0st) hS0ne
  obtain ⟨w1, hw1W, hw10, hw1K⟩ := hW1.2.2.2
  obtain ⟨v1, hv1, hv1eq⟩ := Submodule.mem_map.1 (hW1S hw1W)
  obtain ⟨u1, hu1, rfl⟩ := Submodule.mem_map.1 hv1
  have hgP : ∀ a b, ε a = ε b → ∀ g ∈ piV, (φ ∘ₗ P) (tensV E a b g) = EN a b ((φ ∘ₗ P) g) := by
    intro a b _ g hg
    show φ (P (tensV E a b g)) = EN a b (φ (P g))
    rw [hPcomm]
    exact hφ a b _ (hPmem g (hpiVG g hg))
  have hyP : IsKHWVec ε EN ν1 ((φ ∘ₗ P) u1) := by
    show IsKHWVec ε EN ν1 (φ (P u1))
    rw [hv1eq]; exact hw1K
  obtain ⟨y, hyV, hyK, hyeq⟩ := partialSum_succ_alt hKD (φ ∘ₗ P) hpiVfd hpiVst hgP hu1 hyP
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : (φ ∘ₗ P) 0 = 0 := map_zero _
    rw [h0] at hyeq
    change 0 = φ (P u1) at hyeq
    rw [hv1eq] at hyeq
    exact hw10 hyeq.symm
  obtain ⟨c0, hc0⟩ := Function.ne_iff.1 hy0
  have hwt : ∀ a, E a a (y c0) = (((ν1 - Pi.single c0 1 : Fin n → ℝ) a : ℝ) : ℂ) • y c0 := by
    intro a
    have h1 := congrFun (hyK.1 a) c0
    rw [entry_bounds_of_partialSum, Pi.smul_apply] at h1
    by_cases hac : c0 = a
    · subst hac
      rw [if_pos rfl] at h1
      rw [Pi.sub_apply, Pi.single_eq_same, Complex.ofReal_sub, Complex.ofReal_one, sub_smul,
        one_smul, ← h1]
      abel
    · rw [if_neg hac, add_zero] at h1
      rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hac), sub_zero, h1]
  obtain ⟨u, huV, hu0, huK⟩ := hV.2.2.2
  have hbd1 : ∀ k, kirrPs k ν1 ≤ kirrPs k (lowK ε lam + Pi.single c0 1) := by
    intro k
    have := kirrPs_le hE hV huV hu0 huK (((hpiV_mem y).1 hyV) c0) hc0 hwt k
    rw [partialSum_sub] at this
    rw [rootCone_entry_int]; linarith

  let good : (Fin n → ℝ) → Prop := fun ν =>
    (∃ S : Submodule ℂ (Fin n → D), FiniteDimensional ℂ S ∧ S ≤ X0 ∧ IsKStableSub ε (tensV E) S ∧
      ∃ W ≤ S.map φ, IsKIrrHW ε EN ν W) ∧ ∀ k, kirrPs k ν ≤ kirrPs k (lowK ε lam + Pi.single c0 1)
  have hgoodL : ∀ ν, good ν →
      ∃ M : ℕ, kUnitWtLin ν = kUnitWtLin (lowK ε (lam + Pi.single s 1)) + M := by
    rintro ν ⟨⟨S, hfd, hSX, hSst, W, hWS, hW⟩, -⟩
    obtain ⟨M, hM⟩ := tensorAction_ofLp (hcone S hfd hSX hSst W ν hWS hW)
    exact ⟨M, by rw [unitWeightSum_sub] at hM; linarith⟩
  have hex : ∃ M : ℕ, ∃ ν, good ν ∧ kUnitWtLin ν = kUnitWtLin (lowK ε (lam + Pi.single s 1)) + M := by
    have hg1 : good ν1 := ⟨⟨piV.map P, hS0fd, hS0X, hS0st, W1, hW1S, hW1⟩, hbd1⟩
    obtain ⟨M, hM⟩ := hgoodL ν1 hg1
    exact ⟨M, ν1, hg1, hM⟩
  obtain ⟨ν0, ⟨⟨S1, hS1fd, hS1X, hS1st, W0, hW0S, hW0⟩, hbd0⟩, hL0⟩ := Nat.find_spec hex
  have hmin : ∀ ν, good ν → kUnitWtLin ν0 ≤ kUnitWtLin ν := by
    intro ν hg
    obtain ⟨M, hM⟩ := hgoodL ν hg
    have h1 := Nat.find_min' hex ⟨ν, hg, hM⟩
    have h2 : ((Nat.find hex : ℕ) : ℝ) ≤ M := by exact_mod_cast h1
    rw [hL0, hM]; linarith

  have hcone0 := hcone S1 hS1fd hS1X hS1st W0 ν0 hW0S hW0
  obtain ⟨w0, hw0W, hw00, hw0K⟩ := hW0.2.2.2
  have hdom : ∀ a b : Fin n, a < b → ε a = ε b → ν0 b ≤ ν0 a :=
    fun a b hab hε => highestWeight_dominant hEN hKN hw00 hw0K hab hε
  obtain ⟨hint'', hSA, hGap, hgN, hbig, heq⟩ := shifted_weight_parameter hint hGL hcone0 hbd0 hdom
  have hW0' : IsKIrrHW ε EN (lowK ε (ν0 + rhoC ε - rhoN ε)) W0 := by rw [lowestKType_shift_inv]; exact hW0

  have hsch : ∀ z ∈ Wm ε EN W0, phi EN 1 z = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨z0', hz0W, hz00⟩ := hne
    have : FiniteDimensional ℂ (ncV ε W0 1) := finiteDimensional_ncV hW0.1 1
    have hfdW : FiniteDimensional ℂ (Wm ε EN W0) := Submodule.finiteDimensional_of_le Wm_le_ncV
    have hWst : IsKStableSub ε (bAct EN 1) (Wm ε EN W0) := Wm_kStable hEN hUN hW0'
    have hT'st : IsKStableSub ε EN ((Wm ε EN W0).map (phi EN 1)) := by
      rintro a b hab _ ⟨z, hz, rfl⟩
      rw [← phi_bAct hEN 1 hab z]
      exact Submodule.mem_map_of_mem (hWst a b hab z hz)
    have hT'ne : (Wm ε EN W0).map (phi EN 1) ≠ ⊥ := by
      intro h0
      have : phi EN 1 z0' ∈ (Wm ε EN W0).map (phi EN 1) := Submodule.mem_map_of_mem hz0W
      rw [h0, Submodule.mem_bot] at this
      exact hz00 this
    obtain ⟨W', hW'T, ν', hW'⟩ := exists_kIrreducible_highestWeight hEN hKN inferInstance hT'st hT'ne
    obtain ⟨w', hw'W, hw'0, hw'K⟩ := hW'.2.2.2
    obtain ⟨z0, hz0, hz0eq⟩ := Submodule.mem_map.1 (hW'T hw'W)
    obtain ⟨z1, hz1, -, hkhw1, hfz1⟩ := lift_khw (A := bAct EN 1) (bAct_isKUnitary hUN 1) (phi EN 1)
      (fun a b hab z => phi_bAct hEN 1 hab z) hfdW hWst hz0 (by rw [hz0eq]; exact hw'K)
    have hz10 : z1 ≠ 0 := by
      rintro rfl
      rw [map_zero, hz0eq] at hfz1
      exact hw'0 hfz1.symm
    obtain ⟨a, b, hab, -, hν'⟩ := Wm_khw hEN hUN hW0' hSA hGap hbig hz1 hz10 hkhw1
    rw [lowestKType_shift_inv] at hν'
    let S2 : Submodule ℂ (Fin n → D) := S1 ⊔ ⨆ a : Fin n, ⨆ b : Fin n, S1.map (tensV E a b)
    have hmapmem : ∀ a b z, z ∈ S1 → tensV E a b z ∈ S2 := fun a b z hz =>
      Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
        (Submodule.mem_map_of_mem hz)))
    have hS2fd : FiniteDimensional ℂ S2 := inferInstance
    have hS2X : S2 ≤ X0 := sup_le hS1X (iSup_le fun a => iSup_le fun b => by
      rintro _ ⟨z, hz, rfl⟩
      exact hX0st a b z (hS1X hz))
    have hS2st : IsKStableSub ε (tensV E) S2 := by
      intro c d hcd v hv
      have hle : S2 ≤ S2.comap (tensV E c d) := by
        refine sup_le (fun z hz => Submodule.mem_sup_left (hS1st c d hcd z hz))
          (iSup_le fun a => iSup_le fun b => ?_)
        rintro _ ⟨z, hz, rfl⟩
        show tensV E c d (tensV E a b z) ∈ S2
        have hcm := LinearMap.congr_fun (hT.1 c d a b) z
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hcm
        rw [sub_eq_iff_eq_add] at hcm
        rw [hcm]
        refine S2.add_mem (S2.sub_mem ?_ ?_) (hmapmem a b _ (hS1st c d hcd z hz))
        · split_ifs
          · exact hmapmem _ _ z hz
          · exact S2.zero_mem
        · split_ifs
          · exact hmapmem _ _ z hz
          · exact S2.zero_mem
      exact hle hv
    have hT'le : (Wm ε EN W0).map (phi EN 1) ≤ S2.map φ := by
      rintro _ ⟨z, hz, rfl⟩
      rw [sch_phi_one_apply]
      refine Submodule.sum_mem _ fun p _ => ?_
      have hzp : z (fun _ => p) ∈ W0 := mem_V_of_mem_ncV (Wm_le_ncV hz) _
      obtain ⟨f, hf, hfeq⟩ := Submodule.mem_map.1 (hW0S hzp)
      rw [← hfeq, ← hφ p.1 p.2 f ((hX0mem f).1 (hS1X hf)).1]
      exact Submodule.mem_map_of_mem (hmapmem _ _ f hf)
    have hgood' : good ν' := ⟨⟨S2, hS2fd, hS2X, hS2st, W', hW'T.trans hT'le, hW'⟩, fun k => by
      rw [hν', partialSum_sub]; linarith [partialSum_root_nonneg hab k, hbd0 k]⟩
    have hlt : kUnitWtLin ν' < kUnitWtLin ν0 := by
      rw [hν', unitWeightSum_sub, unitWeightSum_finset_sum hab]
      have hab' : (a : ℕ) < b := hab
      have : (0 : ℝ) < (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (b : ℕ) - (a : ℕ))
      linarith
    exact absurd (hmin ν' hgood') (not_le.2 hlt)

  have hcX : ∀ f ∈ X0, casimir (tensV E) f = ((casVal (lam + Pi.single s 1) : ℝ) : ℂ) • f := by
    intro f hf
    obtain ⟨hfG, hfe⟩ := (hX0mem f).1 hf
    have h1 : (fun c => casimir E (f c)) = ((casVal lam : ℝ) : ℂ) • f :=
      funext fun c => casimir_genSub hE hc (f c) (hfG c)
    rw [hT.2.2.1 f, hfe, h1, casimirValue_add_single]
    push_cast
    rw [add_smul, add_smul, mul_smul]
  have hcas0 : ∀ v ∈ W0, casimir EN v = ((casVal (lam + Pi.single s 1) : ℝ) : ℂ) • v := by
    intro v hv
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 (hW0S hv)
    rw [casimir_map_intertwiner EN φ hφ ((hX0mem f).1 (hS1X hf)).1, hcX f (hS1X hf), map_smul]

  have hsc := schmid_casimir n ε ν0 (h - 2) _ N EN W0 hEN hUN hW0 hsch hcas0 hint'' hSA hGap hgN hp hq
  have hreal : casVal (lam + Pi.single s 1) = casVal (ν0 + rhoC ε - rhoN ε) := by exact_mod_cast hsc
  have hβ0 := cone_norm n (lam + Pi.single s 1) (ν0 - lowK ε (lam + Pi.single s 1)) hmono'.antitone
    hcone0 (by rw [← heq]; unfold casVal at hreal; linarith)
  have hν0 : ν0 = lowK ε (lam + Pi.single s 1) := sub_eq_zero.1 hβ0
  refine ⟨W0, ?_, by rw [← hν0]; exact hW0, hcas0⟩
  rw [← hX0]
  exact hW0S.trans (Submodule.map_mono hS1X)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
