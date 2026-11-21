import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem galois_transitive_on_roots_of_prime (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K))
    (hπ : Prime π) (n : ℕ) (y z : Om l) (hy : y ^ n = ((π : ↥K.1) : Om l))
    (hz : z ^ n = ((π : ↥K.1) : Om l)) (hn : 0 < n) : ∃ g : ↥(GK K), (g : GQ l) y = z := by
  classical

  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : IsFractionRing ↥(OL K) ↥K.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥K.1
  have : IsIntegrallyClosed ↥(OL K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension ℚ_[l]
  have hn0 : n ≠ 0 := hn.ne'
  have hmon : (Polynomial.X ^ n - Polynomial.C π).Monic := Polynomial.monic_X_pow_sub_C π hn0

  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C π) := by
    refine Polynomial.irreducible_of_eisenstein_criterion
      ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ) ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]
      intro h
      exact hπ.not_isUnit (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 h))
    · intro m hm
      rw [Polynomial.degree_X_pow_sub_C hn π, Nat.cast_lt] at hm
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hm.ne]
      split_ifs
      · exact Ideal.sub_mem _ (Ideal.zero_mem _) (Ideal.mem_span_singleton_self π)
      · simp
    · rw [Polynomial.degree_X_pow_sub_C hn π]
      exact_mod_cast hn
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hn0.symm,
        if_pos rfl, zero_sub, Ideal.span_singleton_pow, Ideal.neg_mem_iff, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hπ.not_isUnit
      have h1 : π * 1 = π * (π * c) := by
        rw [mul_one, ← mul_assoc, ← pow_two]
        exact hc
      exact isUnit_of_dvd_one ⟨c, mul_left_cancel₀ hπ.ne_zero h1⟩

  have hirrF : Irreducible (Polynomial.X ^ n - Polynomial.C ((π : ↥K.1))) := by
    have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥K.1)).1 hirr
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at h
  have hmin : ∀ w : Om l, w ^ n = ((π : ↥K.1) : Om l) →
      minpoly (↥K.1) w = Polynomial.X ^ n - Polynomial.C ((π : ↥K.1)) := by
    intro w hw
    refine (minpoly.eq_of_irreducible_of_monic hirrF ?_ (Polynomial.monic_X_pow_sub_C _ hn0)).symm
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      IntermediateField.algebraMap_apply, hw, sub_self]

  have : Normal (↥K.1) (Om l) := Normal.tower_top_of_normal ℚ_[l] (↥K.1) (Om l)
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥K.1) (E := Om l)).1
    ((hmin z hz).trans (hmin y hy).symm)
  refine ⟨⟨σ.restrictScalars ℚ_[l], ?_⟩, hσ⟩
  show σ.restrictScalars ℚ_[l] ∈ IntermediateField.fixingSubgroup K.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact σ.commutes ⟨x, hx⟩

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ (n : ℕ) (y z : Om l), y ^ n = ((π : ↥K.1) : Om l) → z ^ n = ((π : ↥K.1) : Om l) → 0 < n → ∃ g : ↥(GK K), (g : GQ l) y = z := by
  atlas_forward_decl GlobalTheory.galois_transitive_on_roots_of_prime
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isClosed_setOf_gal_apply_eq_padic (l : ℕ) [Fact l.Prime] (a b : Om l) :
    IsClosed {g : GQ l | g a = b} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (MulAction.stabilizer (GQ l) a : Set (GQ l)), ?_,
    (stabilizer_isOpen_of_isIntegral a).preimage (continuous_const.mul continuous_id), ?_⟩
  · intro h hh
    have hs : (g⁻¹ * h) a = a := hh
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hg ⊢
    intro hb
    apply hg
    rw [AlgEquiv.mul_apply] at hs
    have hga := congrArg g hs
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hga
    rw [← hga, hb]
  · show (g⁻¹ * g) a = a
    rw [inv_mul_cancel, AlgEquiv.one_apply]

theorem galois_transitive_on_root_systems_of_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ y z : ℕ → Om l, y 0 = ((π : ↥K.1) : Om l) → z 0 = ((π : ↥K.1) : Om l) → (∀ n, y (n + 1) ^ l = y n) → (∀ n, z (n + 1) ^ l = z n) → ∃ g : ↥(GK K), ∀ n, (g : GQ l) (y n) = z n := by
  intro l _ K π hπ y z hy hz hy' hz'
  have hGK : IsClosed ((GK K : Subgroup (GQ l)) : Set (GQ l)) := by
    unfold GK
    exact InfiniteGalois.fixingSubgroup_isClosed _

  have hpow : ∀ w : ℕ → Om l, (∀ n, w (n + 1) ^ l = w n) → ∀ m k, w (m + k) ^ (l ^ k) = w m := by
    intro w hw m k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul', ← add_assoc, hw, ih]

  let T : ℕ → Set (GQ l) := fun n =>
    (GK K : Set (GQ l)) ∩ ⋂ m, ⋂ (_ : m ≤ n), {g : GQ l | g (y m) = z m}
  have hcl : ∀ n, IsClosed (T n) := fun n =>
    hGK.inter (isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_setOf_gal_apply_eq_padic l (y m) (z m))
  have hdec : ∀ n, T (n + 1) ⊆ T n := by
    rintro n g ⟨h1, h2⟩
    refine ⟨h1, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    exact Set.mem_iInter.1 (Set.mem_iInter.1 h2 m) (Nat.le_succ_of_le hm)
  have hne : ∀ n, (T n).Nonempty := by
    intro n
    have hyn : y n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow y hy' 0 n
      rw [zero_add] at h
      rw [h, hy]
    have hzn : z n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow z hz' 0 n
      rw [zero_add] at h
      rw [h, hz]
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime l K π hπ (l ^ n) (y n) (z n) hyn hzn
      (pow_pos (Fact.out : l.Prime).pos n)
    refine ⟨(g : GQ l), g.2, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    show (g : GQ l) (y m) = z m
    rw [← hpow y hy' m k, ← hpow z hz' m k, map_pow, hg]

  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  refine ⟨⟨g, (Set.mem_iInter.1 hg 0).1⟩, fun n => ?_⟩
  exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hg n).2 n) le_rfl

end GlobalTheory
end
