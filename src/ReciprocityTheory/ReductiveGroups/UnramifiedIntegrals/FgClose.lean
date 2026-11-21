import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TchOfIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SemilinNormPowSubPow
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonH
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgMulN
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffOneSubstOfConstantCoeffEqZero
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnLat
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnWp
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgTorInt
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

def muM : Submonoid ℂ_[l] where
  carrier := muP l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

theorem muM_common (S : Finset (muM l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ a ∈ S, (a : ℂ_[l]) ^ n = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn, hln, hS⟩ := ih
    obtain ⟨m, hm, hlm, ha⟩ := a.2
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · rw [mul_comm, pow_mul, ha, one_pow]
      · rw [pow_mul, hS b hb, one_pow]

theorem muM_exists_gen (n : ℕ) (hn : 0 < n) :
    ∃ g : ℂ_[l], g ^ n = 1 ∧ ∀ a : ℂ_[l], a ^ n = 1 → ∃ k : ℕ, g ^ k = a := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity n ℂ_[l])
  refine ⟨((g : ℂ_[l]ˣ) : ℂ_[l]), ?_, fun a ha => ?_⟩
  · have := g.2
    rw [mem_rootsOfUnity'] at this
    exact this
  · obtain ⟨k, hk⟩ := hg (rootsOfUnity.mkOfPowEq a ha)
    refine ⟨k, ?_⟩
    have := congrArg (fun x : rootsOfUnity n ℂ_[l] => ((x : ℂ_[l]ˣ) : ℂ_[l])) hk
    simpa using this

theorem muM_eval_pow_eq_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n)
    (g : K) (hg : g ^ n = 1) (p : ℤ[X]) (hp : p.eval₂ (Int.castRingHom K) g = 0) :
    p.eval₂ (Int.castRingHom K) (g ^ l) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def] at hp ⊢
  have hd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hg
  have hd0 : 0 < orderOf g := Nat.pos_of_dvd_of_pos hd hn
  have hprim : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
  have hcop : Nat.Coprime l (orderOf g) :=
    ((Fact.out : l.Prime).coprime_iff_not_dvd).2 fun h => hln (h.trans hd)
  have hdvd : minpoly ℤ g ∣ p := minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hd0) hp
  rw [hprim.minpoly_eq_pow_coprime hcop] at hdvd
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (g ^ l))

def phiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] := MonoidAlgebra.lift ℤ ℂ_[l] (muM l) (muM l).subtype

def psiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muM l) ((muM l).subtype.comp (powMonoidHom l))

theorem phiM_ker_le (f : MonoidAlgebra ℤ (muM l)) (hf : phiM l f = 0) : psiM l f = 0 := by
  classical
  obtain ⟨n, hn, hln, hS⟩ := muM_common l f.coeff.support
  obtain ⟨g, hg, hgen⟩ := muM_exists_gen l n hn
  have hk : ∀ a : muM l, ∃ k : ℕ, a ∈ f.coeff.support → g ^ k = (a : ℂ_[l]) := by
    intro a
    by_cases ha : a ∈ f.coeff.support
    · obtain ⟨k, hk⟩ := hgen a (hS a ha)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose k hk using hk
  let p : ℤ[X] := ∑ a ∈ f.coeff.support, C (f.coeff a) * X ^ (k a)
  have h1 : p.eval₂ (Int.castRingHom ℂ_[l]) g = 0 := by
    rw [← hf, phiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hk a ha]
    simp [zsmul_eq_mul]
  have h2 := muM_eval_pow_eq_zero l n hn hln g hg p h1
  rw [← h2, psiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul, mul_comm l, pow_mul, hk a ha]
  simp [zsmul_eq_mul]

theorem phiM_mem (f : MonoidAlgebra ℤ (muM l)) : phiM l f ∈ Rmu l := by
  rw [phiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure a.2) _

theorem psiM_mem (f : MonoidAlgebra ℤ (muM l)) : psiM l f ∈ Rmu l := by
  rw [psiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure (a ^ l).2) _

theorem phiM_surj (x : ℂ_[l]) (hx : x ∈ Rmu l) : ∃ f, phiM l f = x := by
  have : Rmu l ≤ (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).range := by
    refine Subring.closure_le.2 fun ζ hζ => ⟨MonoidAlgebra.single ⟨ζ, hζ⟩ 1, ?_⟩
    simp [phiM]
  exact this hx

theorem rmu_sigma : ∃ s : Rmu l →+* Rmu l,
    ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l), ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l := by
  let φ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (phiM_mem l)
  let ψ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (psiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (psiM_mem l)
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf⟩ := phiM_surj l x hx
    exact ⟨f, Subtype.ext hf⟩
  have hker : RingHom.ker φ ≤ RingHom.ker ψ := by
    intro f hf
    rw [RingHom.mem_ker] at hf ⊢
    exact Subtype.ext (phiM_ker_le l f (congrArg Subtype.val hf))
  refine ⟨RingHom.liftOfSurjective φ hφ ⟨ψ, hker⟩, fun ζ hζ => ?_⟩
  have h1 : (⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) = φ (MonoidAlgebra.single ⟨ζ, hζ⟩ 1) :=
    Subtype.ext (by simp [φ, phiM])
  rw [h1, RingHom.liftOfRightInverse_comp_apply]
  simp [ψ, psiM]

theorem rmu_sigma_congr (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ∃ r ∈ Rmu l, ((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l = (l : ℂ_[l]) * r := by
  have hl : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Rmu l), ∃ r : Rmu l, s ⟨y, hy⟩ - ⟨y, hy⟩ ^ l = (l : Rmu l) * r := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem ζ hζ => exact ⟨0, Subtype.ext (by simp [hs ζ hζ])⟩
    | zero =>
      refine ⟨0, ?_⟩
      have : (⟨0, zero_mem _⟩ : Rmu l) = 0 := rfl
      rw [this, map_zero, zero_pow hl.ne_zero]; simp
    | one =>
      refine ⟨0, ?_⟩
      have : (⟨1, one_mem _⟩ : Rmu l) = 1 := rfl
      rw [this, map_one, one_pow]; simp
    | add a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      obtain ⟨u, hu⟩ := exists_add_pow_prime_eq hl (⟨a, ha⟩ : Rmu l) ⟨b, hb⟩
      refine ⟨r + t - ⟨a, ha⟩ * ⟨b, hb⟩ * u, ?_⟩
      have : (⟨a + b, add_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this, map_add, hu]
      linear_combination hr + ht
    | neg a ha iha =>
      obtain ⟨r, hr⟩ := iha
      have : (⟨-a, neg_mem ha⟩ : Rmu l) = -⟨a, ha⟩ := rfl
      rw [this, map_neg]
      rcases hl.eq_two_or_odd' with h2 | hodd
      · refine ⟨-r - ⟨a, ha⟩ ^ 2, ?_⟩
        subst h2
        push_cast at hr ⊢
        linear_combination -hr
      · refine ⟨-r, ?_⟩
        rw [hodd.neg_pow]
        linear_combination -hr
    | mul a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      refine ⟨r * s ⟨b, hb⟩ + ⟨a, ha⟩ ^ l * t, ?_⟩
      have : (⟨a * b, mul_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, mul_pow]
      linear_combination s ⟨b, hb⟩ * hr + ⟨a, ha⟩ ^ l * ht
  obtain ⟨r, hr⟩ := key x.1 x.2
  refine ⟨r, r.2, ?_⟩
  have := congrArg (Subtype.val) hr
  simpa using this

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem norm_prime_lt_one_padicField : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_l_Cl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_prime_pos_padicField : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_l_Cl]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)

theorem frobeniusLift_near_pow (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨r, hr, h⟩ := rmu_sigma_congr l s hs x
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

theorem frobeniusLift_norm_one (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l)
    (hx : ‖(x : ℂ_[l])‖ = 1) : ‖((s x : Rmu l) : ℂ_[l])‖ = 1 := by
  have h1 : ‖(x : ℂ_[l]) ^ l‖ = 1 := by rw [norm_pow, hx, one_pow]
  have h2 : ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ < ‖(x : ℂ_[l]) ^ l‖ := by
    rw [h1]; exact lt_of_le_of_lt (frobeniusLift_near_pow l s hs x) (norm_prime_lt_one_padicField l)
  have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h2)
  rw [sub_add_cancel, max_eq_right h2.le, h1] at h3
  exact h3

theorem unitBall_eq_frac_normOne {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖b‖ = 1 ∧ x * b = a := by
  by_cases hx0 : x = 0
  · exact ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, norm_one, by simp [hx0]⟩
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l hx hx0
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖x‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd h1 (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  refine ⟨(l : ℂ_[l]) ^ k * a, (Rmu l).mul_mem ((Rmu l).pow_mem (natCast_mem _ l) k) ha,
    b, hb, hnb, ?_⟩
  rw [h, zpow_natCast]
  field_simp

theorem rmu_sigma_norm (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : (x : ℂ_[l]) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l (rmu_le_kmu l x.2) hx0'
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖(x : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd (rmu_norm_le l x.2) (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have he : x * (⟨b, hb⟩ : Rmu l) = (l : Rmu l) ^ k * (⟨a, ha⟩ : Rmu l) := by
    apply Subtype.ext
    push_cast
    rw [h, zpow_natCast]
    field_simp
  have hs' := congrArg (fun z : Rmu l => ‖(z : ℂ_[l])‖) (congrArg s he)
  simp only [map_mul, map_pow, map_natCast] at hs'
  push_cast at hs'
  rw [norm_mul, norm_mul, norm_pow, frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb,
    frobeniusLift_norm_one l s hs ⟨a, ha⟩ hna, mul_one, mul_one] at hs'
  rw [hs', hn, zpow_natCast]

section Generic

variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)

def subringInclusionSubfield : R →+* F := Subring.inclusion h

theorem subringInclusionSubfield_coe (x : R) : ((subringInclusionSubfield R F h x : F) : K) = (x : K) := rfl

theorem subringInclusionSubfield_injective : Function.Injective (subringInclusionSubfield R F h) := fun x y e =>
  Subtype.ext (by rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, e])

theorem isFractionRing_subringInclusion (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b) :
    @IsFractionRing R _ F _ (subringInclusionSubfield R F h).toAlgebra := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : FaithfulSMul R F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (subringInclusionSubfield_injective R F h)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, ha, b, hb, -, e⟩ := hf z z.2
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext ?_⟩
  rw [Subfield.coe_div, e]
  rfl

theorem exists_extend_endomorphism_fractions (h : R ≤ F.toSubring) (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b)
    (s : R →+* R) (hsinj : Function.Injective s) :
    ∃ σ : F →+* F, ∀ (x : F) (a b : R), (x : K) * b = a →
      ((σ x : F) : K) * (s b : R) = (s a : R) := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : IsFractionRing R F := isFractionRing_subringInclusion R F h hf
  have hg : Function.Injective ((subringInclusionSubfield R F h).comp s) := (subringInclusionSubfield_injective R F h).comp hsinj
  have hσ : ∀ x : R, IsFractionRing.lift hg (subringInclusionSubfield R F h x) = subringInclusionSubfield R F h (s x) :=
    fun x => IsFractionRing.lift_algebraMap hg x
  refine ⟨IsFractionRing.lift hg, fun x a b e => ?_⟩
  have h' : x * subringInclusionSubfield R F h b = subringInclusionSubfield R F h a :=
    Subtype.ext (by rw [Subfield.coe_mul, subringInclusionSubfield_coe, subringInclusionSubfield_coe, e])
  have h2 := congrArg (IsFractionRing.lift hg) h'
  rw [map_mul, hσ, hσ] at h2
  rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, ← Subfield.coe_mul, h2]

end Generic

theorem frobeniusLift_injective (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := rmu_sigma_norm l s hs x
  rw [hx, Subring.coe_zero, norm_zero] at this
  exact Subtype.ext (norm_eq_zero.mp this.symm)

theorem norm_unramifiedField_coe (x : Kmu l) : ‖x‖ = ‖(x : ℂ_[l])‖ := rfl

theorem kmu_sigma : ∃ s : Kmu l →+* Kmu l, (∀ x : Kmu l, ‖s x‖ = ‖x‖) ∧
    ∀ x : Kmu l, ‖x‖ ≤ 1 → ‖s x - x ^ l‖ ≤ ‖(l : Kmu l)‖ := by
  obtain ⟨s, hs⟩ := rmu_sigma l
  obtain ⟨σ, key⟩ := exists_extend_endomorphism_fractions (Rmu l) (Kmu l) (fun _ hx => rmu_le_kmu l hx)
    (fun _ hx => kmu_frac l hx) s (frobeniusLift_injective l s hs)
  refine ⟨σ, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, b, hb, hb0, h⟩ := kmu_frac l x.2
    have h1 : (x : ℂ_[l]) * b = a := by rw [h]; field_simp
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have h3 := congrArg norm h2
    have h4 := congrArg norm h1
    rw [norm_mul, rmu_sigma_norm l s hs, rmu_sigma_norm l s hs] at h3
    rw [norm_mul] at h4
    have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe]
    exact mul_right_cancel₀ hb' (h3.trans h4.symm)
  · intro x hx
    rw [norm_unramifiedField_coe] at hx
    obtain ⟨a, ha, b, hb, hnb, h1⟩ := unitBall_eq_frac_normOne l x.2 hx
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have hsb := frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb
    have hna := frobeniusLift_near_pow l s hs ⟨a, ha⟩
    have hnb' := frobeniusLift_near_pow l s hs ⟨b, hb⟩
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe, Subfield.coe_sub, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    generalize ((s ⟨a, ha⟩ : Rmu l) : ℂ_[l]) = sa at h2 hna
    generalize ((s ⟨b, hb⟩ : Rmu l) : ℂ_[l]) = sb at h2 hnb' hsb
    generalize ((σ x : Kmu l) : ℂ_[l]) = y at h2 ⊢
    simp only at hna hnb'
    have e : (y - (x : ℂ_[l]) ^ l) * sb = (sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l)) := by
      rw [← h1, ← h2]; ring
    have hxl : ‖(x : ℂ_[l]) ^ l‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have e2 : ‖(y - (x : ℂ_[l]) ^ l)‖ = ‖(sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))‖ := by
      rw [← e, norm_mul, hsb, mul_one]
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hna ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hxl).trans hnb'

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

def kmuIncl : Kmu l →+* MaximalUnramifiedExtension l := Subfield.inclusion (Subfield.le_topologicalClosure (Kmu l))

theorem kmuIncl_norm (x : Kmu l) : ‖kmuIncl l x‖ = ‖x‖ := rfl

theorem kmuIncl_isometry : Isometry (kmuIncl l) :=
  AddMonoidHomClass.isometry_of_norm (kmuIncl l) (fun x => kmuIncl_norm l x)

theorem kmuIncl_denseRange : DenseRange (kmuIncl l) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨y, hy, hxy⟩ := kur_approx l x.2 e he
  exact ⟨kmuIncl l ⟨y, hy⟩, ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hxy⟩

theorem kurFrob : ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ := by
  obtain ⟨s, hs1, hs2⟩ := kmu_sigma l
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  have hiso : Isometry ((kmuIncl l).comp s) :=
    AddMonoidHomClass.isometry_of_norm _ (fun x => by
      rw [RingHom.comp_apply, kmuIncl_norm, hs1])
  let σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l :=
    IsDenseInducing.extendRingHom (i := kmuIncl l) (f := (kmuIncl l).comp s)
      (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous
  have hdi : IsDenseInducing (kmuIncl l) :=
    (kmuIncl_isometry l).isUniformInducing.isDenseInducing (kmuIncl_denseRange l)
  have hσc : Continuous σ :=
    (uniformContinuous_uniformly_extend (kmuIncl_isometry l).isUniformInducing
      (kmuIncl_denseRange l) hiso.uniformContinuous).continuous
  have hσi : ∀ x : Kmu l, σ (kmuIncl l x) = kmuIncl l (s x) := fun x =>
    hdi.extend_eq hiso.continuous x
  have hl : ‖(l : MaximalUnramifiedExtension l)‖ = ‖(l : ℂ_[l])‖ := rfl
  refine ⟨σ, Fact.out, ?_, ?_, ?_, ?_⟩
  · rw [hl, norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  · intro x
    refine (kmuIncl_denseRange l).induction_on (p := fun x => ‖σ x‖ = ‖x‖) x
      (isClosed_eq hσc.norm continuous_norm) (fun y => ?_)
    rw [hσi, kmuIncl_norm, kmuIncl_norm, hs1]
  · intro x hx
    have hopen : IsOpen (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hmem : x ∈ closure (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1 ∩ Set.range (kmuIncl l)) :=
      (kmuIncl_denseRange l).open_subset_closure_inter hopen (by simpa using hx)
    have hcl : IsClosed {x : MaximalUnramifiedExtension l | ‖σ x - x ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖} :=
      isClosed_le (hσc.sub (continuous_pow l)).norm continuous_const
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hy1, y, rfl⟩
    have hy : ‖y‖ ≤ 1 := by
      rw [mem_closedBall_zero_iff, kmuIncl_norm] at hy1
      exact hy1
    have := hs2 y hy
    show ‖σ (kmuIncl l y) - (kmuIncl l y) ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖
    rw [hσi, ← map_pow, ← map_sub, kmuIncl_norm]
    exact this
  · intro x hx
    exact kur_discrete l x.2 hx

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem FrobField.funEqSetting_sq [CompleteSpace K] (h : FrobField K l σ) :
    FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) :=
  ⟨h.prime, ⟨2, two_pos, rfl⟩, h.norm_l, fun a ha => h.norm_sq_sub_pow_le a ha⟩

omit [IsUltrametricDist K] [CharZero K] in

theorem ltLog_sub_eq_X (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : PowerSeries K) ^ (l ^ 2))
      = X := by
  have hq : 2 ≤ l ^ 2 := by nlinarith
  have hq0 : l ^ 2 ≠ 0 := by omega
  have hsub : ∀ (f : PowerSeries K) {k : ℕ} (_ : k ≠ 0) (m : ℕ),
      coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
    intro f k hk m
    have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
    rw [PowerSeries.coeff_subst' ha]
    simp only [← pow_mul, PowerSeries.coeff_X_pow]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [finsum_eq_single _ q]
      · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
      · intro d hd
        have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
        simp [this]
    · rw [finsum_eq_zero_of_forall_eq_zero]
      intro d
      have : m ≠ k * d := fun h => hd ⟨d, h⟩
      simp [this]
  have hpow : ∀ j, coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
    intro j
    have hex : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
    rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_pos hex]
    have hf : Nat.find hex = j := (Nat.pow_right_injective hq (Nat.find_spec hex)).symm
    rw [hf]
  ext n
  rw [map_sub, PowerSeries.coeff_smul, hsub _ hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    rcases j with _ | j
    · have h1 : (l ^ 2) ^ 0 = 1 := pow_zero _
      have hnd : ¬ l ^ 2 ∣ (l ^ 2) ^ 0 := by
        rw [h1]
        intro h
        have := Nat.le_of_dvd one_pos h
        omega
      rw [if_neg hnd, hpow 0, h1, if_pos rfl]
      simp
    · have hd : l ^ 2 ∣ (l ^ 2) ^ (j + 1) := dvd_pow_self _ (Nat.succ_ne_zero j)
      have hdiv : (l ^ 2) ^ (j + 1) / l ^ 2 = (l ^ 2) ^ j := by
        rw [pow_succ (l ^ 2) j, Nat.mul_div_cancel _ (by omega)]
      have hne : (l ^ 2) ^ (j + 1) ≠ 1 := by
        have : l ^ 2 ≤ (l ^ 2) ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) _
        omega
      rw [if_pos hd, hdiv, PowerSeries.coeff_map, hpow, hpow,
        if_neg hne, map_inv₀, map_pow, map_natCast, pow_succ (l : K) j, mul_inv]
      ring
  · have h0 : coeff n (ltLog K l) = 0 := by rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_neg hn]
    have hX : n ≠ 1 := fun h => hn ⟨0, by rw [h, pow_zero]⟩
    rw [h0, if_neg hX]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have hm : ¬ ∃ j, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj, pow_succ (l ^ 2) j, mul_comm]⟩
      rw [Nat.mul_div_cancel_left m (by omega), PowerSeries.coeff_map, Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk,
        dif_neg hm, map_zero]
      simp
    · simp

theorem ltLog_type (hl : 2 ≤ l) (τ : K →+* K) : IsFunEqType l (l ^ 2) τ (ltLog K l) := by
  unfold IsFunEqType
  rw [ltLog_sub_eq_X hl τ]
  exact integralPS_X

omit [IsUltrametricDist K] [CharZero K] in

theorem isFunEqType_of_mv {p q : ℕ} (hq : q ≠ 0) (τ : K →+* K) (f : PowerSeries K)
    (h : IsFunEqTypeMv (ι := Unit) p q hq τ f) : IsFunEqType p q τ f := by
  unfold IsFunEqType IsFunEqTypeMv at *
  have he : (PowerSeries.map τ f).subst ((X : PowerSeries K) ^ q)
      = MvPowerSeries.expand q hq (MvPowerSeries.map τ f) := by
    first
    | rfl
    | exact (MvPowerSeries.expand_eq_subst _ _ _).symm
    | (simp only [MvPowerSeries.expand, PowerSeries.subst]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; congr 1)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom, PowerSeries.subst]; congr 1)
  rw [he]
  unfold IntegralPS
  intro n
  first
  | exact h (Finsupp.single () n)
  | exact (by unfold IntegralMv at h; exact h (Finsupp.single () n))

omit [IsUltrametricDist K] [CharZero K] in
theorem inv_mul_inv_eq_of_eq_mul (c ε t x : K) (hc : c ≠ 0) (h : ε = c * t) :
    x⁻¹ * t⁻¹ = ε⁻¹ * (c / x) := by
  rw [h, mul_inv, div_eq_mul_inv]
  calc x⁻¹ * t⁻¹ = (c⁻¹ * c) * (t⁻¹ * x⁻¹) := by rw [inv_mul_cancel₀ hc, one_mul, mul_comm]
    _ = c⁻¹ * t⁻¹ * (c * x⁻¹) := by ring

theorem fin_integral [CompleteSpace K] (hF : FrobField K l σ) (ex lam : PowerSeries K)
    (hlam0 : constantCoeff lam = 0) (hlam1 : coeff 1 lam = 1) (hex0 : constantCoeff ex = 0)
    (hinv : ex.subst lam = X) (c ε : K) (hc : ‖c‖ = 1) (hε : ‖ε‖ = 1) (hcε : ε = c * σ (σ ε))
    (hT : IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    IntegralPS (ex.subst (C ε * ltLog K l)) := by
  have hl2 : 2 ≤ l := hF.prime.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hF.prime.ne_zero
  have hS := hF.funEqSetting_sq
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hτε0 : σ (σ ε) ≠ 0 := fun h => hε0 (by rw [hcε, h, mul_zero])
  have hXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) := PowerSeries.HasSubst.X_pow hq

  set f0 : PowerSeries K := ε⁻¹ • lam with hf0
  have hf00 : constantCoeff f0 = 0 := by
    rw [hf0, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      coeff_zero_eq_constantCoeff_apply, hlam0, smul_zero]
  have hf0T : IsFunEqType l (l ^ 2) (σ.comp σ) f0 := by
    unfold IsFunEqType
    have e : f0 - (l : K)⁻¹ • (PowerSeries.map (σ.comp σ) f0).subst ((X : PowerSeries K) ^ (l ^ 2))
        = C ε⁻¹ * (lam - (c / (l : K)) •
          (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
      have e1 : PowerSeries.map (σ.comp σ) f0 = (σ (σ ε))⁻¹ • PowerSeries.map (σ.comp σ) lam := by
        ext n
        rw [hf0, coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_map, smul_eq_mul,
          smul_eq_mul, map_mul, map_inv₀]
        rfl
      rw [e1, PowerSeries.subst_smul hXq, smul_smul, ← smul_eq_C_mul, smul_sub, smul_smul, hf0]
      congr 2
      have hc0 : c ≠ 0 := fun h => by simp [h] at hc
      exact inv_mul_inv_eq_of_eq_mul c ε _ _ hc0 hcε
    rw [e]
    exact integralPS_mul (integralPS_C (by rw [norm_inv, hε, inv_one])) hT

  set α : PowerSeries K := C ε * X with hα
  have hα0 : constantCoeff α = 0 := by rw [hα, map_mul, constantCoeff_X, mul_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hαI : IntegralPS α := integralPS_mul (integralPS_C hε.le) integralPS_X
  set f1 : PowerSeries K := f0.subst α with hf1
  have hf1T : IsFunEqType l (l ^ 2) (σ.comp σ) f1 :=
    isFunEqType_of_mv hq _ _ (Formalism.LT.funEqSubst K l (l ^ 2) hq (σ.comp σ) hS f0 hf00 hf0T Unit α
      hα0 ((integralPS_iff_mv α).1 hαI))
  have hf1e : f1 = ε⁻¹ • PowerSeries.rescale ε lam := by
    rw [hf1, hf0, PowerSeries.subst_smul hαs, PowerSeries.rescale_eq_subst, hα, ← smul_eq_C_mul]
  have hf10 : constantCoeff f1 = 0 := by
    rw [hf1e, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, hlam0]; simp
  have hf11 : coeff 1 f1 = 1 := by
    rw [hf1e, PowerSeries.coeff_smul, coeff_rescale, hlam1, pow_one, mul_one, smul_eq_mul,
      inv_mul_cancel₀ hε0]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ.comp σ) hS f1 (ltLog K l) hf10 hf11
    hf1T (ltLog_const l hl2) (ltLog_type hl2 _)
  have hhs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hβ0 : constantCoeff (C ε * h) = 0 := by rw [map_mul, hh0, mul_zero]
  have hβs : PowerSeries.HasSubst (C ε * h) := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have hlams : PowerSeries.HasSubst lam := PowerSeries.HasSubst.of_constantCoeff_zero' hlam0
  have e2 : α.subst h = C ε * h := by
    rw [hα, PowerSeries.subst_mul hhs, PowerSeries.subst_X hhs, PowerSeries.subst_C]; rfl
  have e3 : lam.subst (C ε * h) = C ε * ltLog K l := by
    rw [← hh, hf1, PowerSeries.subst_comp_subst_apply hαs hhs, e2, hf0,
      PowerSeries.subst_smul hβs, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hε0,
      map_one, one_mul]
  rw [← e3, ← PowerSeries.subst_comp_subst_apply hlams hβs, hinv, PowerSeries.subst_X hβs]
  exact integralPS_mul (integralPS_C hε.le) hhI

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem trans_ev (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    ∀ᶠ z in nhds (0 : ℂ), z + t ∉ L.lattice := by
  have ho : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hc : ContinuousAt (fun z : ℂ => z + t) 0 := by fun_prop
  have : (L.lattice : Set ℂ)ᶜ ∈ nhds ((fun z : ℂ => z + t) 0) := by
    apply ho.mem_nhds
    simpa using ht
  exact hc.eventually this

theorem trans_an (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    AnalyticAt ℂ (fun z => L.weierstrassP (z + t)) 0 ∧
      AnalyticAt ℂ (fun z => L.derivWeierstrassP (z + t)) 0 := by
  have h1 : AnalyticAt ℂ L.weierstrassP ((fun z : ℂ => z + t) 0) :=
    L.analyticOnNhd_weierstrassP _ (by simpa using ht)
  have h2 : AnalyticAt ℂ L.derivWeierstrassP ((fun z : ℂ => z + t) 0) :=
    L.analyticOnNhd_derivWeierstrassP _ (by simpa using ht)
  have h3 : AnalyticAt ℂ (fun z : ℂ => z + t) 0 := by fun_prop
  exact ⟨AnalyticAt.comp (g := L.weierstrassP) (f := fun z : ℂ => z + t) h1 h3,
    AnalyticAt.comp (g := L.derivWeierstrassP) (f := fun z : ℂ => z + t) h2 h3⟩

theorem trans_taylor_quad (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b : ℂ) :
    F.taylor0 (fun z => a * (f z * f z) + b) = C a * (F.taylor0 f * F.taylor0 f) + C b := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff : AnalyticAt ℂ (fun z => f z * f z) 0 := hf.mul hf
  have haff : AnalyticAt ℂ (fun z => a * (f z * f z)) 0 := analyticAt_const.mul hff
  have h1 := (hR f f hf hf).2
  have h2 := (hR (fun _ => a) (fun z => f z * f z) analyticAt_const hff).2
  have h3 := (hR (fun z => a * (f z * f z)) (fun _ => b) haff analyticAt_const).1
  rw [h3, h2, h1, hC, hC]

theorem trans_taylor_cubic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b c : ℂ) :
    F.taylor0 (fun z => a * (f z * (f z * f z)) + (b * f z + c))
      = C a * (F.taylor0 f * (F.taylor0 f * F.taylor0 f)) + (C b * F.taylor0 f + C c) := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff : AnalyticAt ℂ (fun z => f z * f z) 0 := hf.mul hf
  have hfff : AnalyticAt ℂ (fun z => f z * (f z * f z)) 0 := hf.mul hff
  have hafff : AnalyticAt ℂ (fun z => a * (f z * (f z * f z))) 0 := analyticAt_const.mul hfff
  have hbf : AnalyticAt ℂ (fun z => b * f z) 0 := analyticAt_const.mul hf
  have hbfc : AnalyticAt ℂ (fun z => b * f z + c) 0 := hbf.add analyticAt_const
  have h1 := (hR f f hf hf).2
  have h2 := (hR f (fun z => f z * f z) hf hff).2
  have h3 := (hR (fun _ => a) (fun z => f z * (f z * f z)) analyticAt_const hfff).2
  have h4 := (hR (fun _ => b) f analyticAt_const hf).2
  have h5 := (hR (fun z => b * f z) (fun _ => c) hbf analyticAt_const).1
  have h6 := (hR (fun z => a * (f z * (f z * f z))) (fun z => b * f z + c) hafff hbfc).1
  rw [h6, h5, h4, h3, h2, h1, hC, hC, hC]

theorem trans_taylor (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    derivative ℂ (F.taylor0 (fun z => L.weierstrassP (z + t)))
        = F.taylor0 (fun z => L.derivWeierstrassP (z + t)) ∧
    derivative ℂ (F.taylor0 (fun z => L.derivWeierstrassP (z + t)))
        = C 6 * (F.taylor0 (fun z => L.weierstrassP (z + t))
            * F.taylor0 (fun z => L.weierstrassP (z + t))) + C (-(L.g₂ / 2)) ∧
    F.taylor0 (fun z => L.derivWeierstrassP (z + t)) * F.taylor0 (fun z => L.derivWeierstrassP (z + t))
        = C 4 * (F.taylor0 (fun z => L.weierstrassP (z + t))
            * (F.taylor0 (fun z => L.weierstrassP (z + t))
              * F.taylor0 (fun z => L.weierstrassP (z + t))))
          + (C (-L.g₂) * F.taylor0 (fun z => L.weierstrassP (z + t)) + C (-L.g₃)) := by
  obtain ⟨haf, hag⟩ := trans_an L t ht
  obtain ⟨hR, hC, -, hG⟩ := F.taylorRing
  obtain ⟨hD, -, -⟩ := F.taylorDeriv
  have hev := trans_ev L t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [← hD _ haf]
    congr 1
    funext z
    rw [deriv_comp_add_const, L.deriv_weierstrassP]
  · rw [← hD _ hag, ← trans_taylor_quad _ haf]
    apply hG
    filter_upwards [hev] with z hz
    rw [deriv_comp_add_const, (F.pSecond L (z + t) hz).deriv]
    ring
  · rw [← (hR _ _ hag hag).2, ← trans_taylor_cubic _ haf]
    apply hG
    filter_upwards [hev] with z hz
    have := L.derivWeierstrassP_sq (z + t) hz
    linear_combination this

theorem trans_derivative_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    derivative S (PowerSeries.map φ f) = PowerSeries.map φ (derivative R f) := by
  ext n
  simp [coeff_derivative]

theorem trans_constSubst {K : Type*} [CommRing K] (f a : K⟦X⟧) (ha : constantCoeff a = 0) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have h1 := constantCoeff_subst_eq_zero (S := K) ha (f - C (constantCoeff f)) h0
  rw [subst_sub hs, subst_C] at h1
  have h2 : constantCoeff (subst a f - C (constantCoeff f)) = 0 := h1
  rw [map_sub, constantCoeff_C, sub_eq_zero] at h2
  exact h2

theorem trans_plus_const {K : Type} [Field K] (g2 g3 xP yP : K) :
    constantCoeff (A.yPlus (A.shortW g2 g3) xP yP) = yP ∧
    constantCoeff (A.xPlus (A.shortW g2 g3) xP yP) = xP := by
  obtain ⟨-, -, -, hx, hy⟩ := A.wSerFactor K (A.shortW g2 g3)
  have ht : constantCoeff (A.tDen (A.shortW g2 g3) xP) = 1 := by simp [A.tDen, hx]
  have h1 : (A.shortW g2 g3).a₁ = 0 := rfl
  have h3 : (A.shortW g2 g3).a₃ = 0 := rfl
  constructor
  · simp [A.yPlus, A.xPlus, A.nS, hx, hy, ht, h1, h3]
    ring
  · simp [A.xPlus]

theorem trans_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ)
    (ht : t ∉ L.lattice) :
    PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 (fun z => L.weierstrassP (z + t)))
      = (A.xPlus (A.shortW (ι L.g₂) (ι L.g₃)) (ι (L.weierstrassP t))
          (ι (L.derivWeierstrassP t) / 2)).subst (A.expSer (A.shortW (ι L.g₂) (ι L.g₃))) := by
  obtain ⟨e1, e2, e3⟩ := trans_taylor L t ht
  set p := F.taylor0 (fun z => L.weierstrassP (z + t)) with hp
  set q := F.taylor0 (fun z => L.derivWeierstrassP (z + t)) with hq
  set W := A.shortW (ι L.g₂) (ι L.g₃) with hW
  have a1 : W.a₁ = 0 := rfl
  have a2 : W.a₂ = 0 := rfl
  have a3 : W.a₃ = 0 := rfl
  have a4 : W.a₄ = -ι L.g₂ / 4 := rfl
  have a6 : W.a₆ = -ι L.g₃ / 4 := rfl
  have hpt : W.toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    rw [WeierstrassCurve.Affine.equation_iff, a1, a2, a3, a4, a6]
    have := congrArg ι (L.derivWeierstrassP_sq t ht)
    simp only [map_pow, map_sub, map_mul, map_ofNat] at this
    linear_combination (1 / 4 : ℂ_[l]) * this
  obtain ⟨hfl, -, -⟩ := A.plusZ ℂ_[l] W _ _ hpt
  set P := PowerSeries.map (ι : ℂ →+* ℂ_[l]) p with hP
  set Q := PowerSeries.map (ι : ℂ →+* ℂ_[l]) q with hQ
  have i2 : ι 2 = 2 := map_ofNat ι 2
  have i4 : ι 4 = 4 := map_ofNat ι 4
  have i6 : ι 6 = 6 := map_ofNat ι 6
  have E1 : derivative ℂ_[l] P = Q := by rw [hP, trans_derivative_map, e1]
  have E2 : derivative ℂ_[l] Q = C 6 * (P * P) + C (-(ι L.g₂ / 2)) := by
    rw [hQ, trans_derivative_map, e2]
    simp [hP, i2, i6]
  have E3 : Q * Q = C 4 * (P * (P * P)) + (C (-ι L.g₂) * P + C (-ι L.g₃)) := by
    rw [hQ, ← map_mul, e3]
    simp [hP, i4]
  have h2 : (C (1 / 2 : ℂ_[l]) : ℂ_[l]⟦X⟧) * 2 = 1 := by
    rw [← map_ofNat (C : ℂ_[l] →+* ℂ_[l]⟦X⟧) 2, ← map_mul]
    norm_num
  have hfl' : A.IsFlow (A.curveS W) (derivative ℂ_[l]) P (C (1 / 2 : ℂ_[l]) * Q) := by
    have c4 : (C (-ι L.g₂ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul, ← map_mul]; congr 1; ring
    have c6 : (C (-ι L.g₃ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₃) := by
      rw [← map_mul, ← map_mul]; congr 1; ring
    have c2 : (C (-(ι L.g₂ / 2)) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul]; congr 1; ring
    have k4 : (C 4 : ℂ_[l]⟦X⟧) = 4 := map_ofNat _ 4
    have k6 : (C 6 : ℂ_[l]⟦X⟧) = 6 := map_ofNat _ 6
    refine ⟨?_, ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, a1, a2, a3, a4, a6, map_zero, c4, c6]
      rw [k4] at E3
      linear_combination (C (1 / 2 : ℂ_[l]) * C (1 / 2)) * E3 +
        (P ^ 3 * (C (1 / 2 : ℂ_[l]) * 2 + 1)) * h2
    · simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, a1, a3, map_zero]
      rw [E1]
      linear_combination (-Q) * h2
    · simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
        a1, a2, a4, map_zero, c4]
      rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul, E2, k6, c2]
      linear_combination (3 * P ^ 2) * h2
  have hc0 : constantCoeff (A.expSer W) = 0 := (A.expSpec ℂ_[l] W).1
  refine (A.flowUniqueZ ℂ_[l] W _ _ _ _ hfl' hfl ?_ ?_).1
  · rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).2, hP, hp]
    simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
  · rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).1, hQ, hq]
    simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
    ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem endo_curve (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    ∃ neg : S → S, C.IsEndoCurve (A.shortW (ι L.g₂) (ι L.g₃)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (fun P : S => ι (L.derivWeierstrassP (P : ℂ)) / 2)
      (ι α) := by
  obtain ⟨neg, hneg, hinv, -, hid⟩ := F.endoZInstance L α S hα hst hS
  have hb2 : (A.shortW (ι L.g₂) (ι L.g₃)).b₂ = 0 := by
    simp [A.shortW, WeierstrassCurve.b₂]
  have hnegeq : ∀ P : S, (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ) := by
    intro P
    simp
  refine ⟨neg, ?_, hinv, ?_, ?_⟩
  · intro P
    have h := L.derivWeierstrassP_sq (P : ℂ) (hS.1 P P.2).2
    have h' := congrArg ι h
    simp only [map_pow, map_sub, map_mul, map_ofNat] at h'
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW]
    linear_combination (1 / 4 : ℂ_[l]) * h'
  · intro P
    constructor
    · show ι (L.weierstrassP (neg P : ℂ)) = _
      rw [hnegeq P, L.weierstrassP_add_coe, L.weierstrassP_neg]
    · show ι (L.derivWeierstrassP (neg P : ℂ)) / 2 = _
      rw [hnegeq P, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]
      simp [WeierstrassCurve.Affine.negY, A.shortW, neg_div]
  · have h := congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[l])) hid
    rw [wp_bridge]
    simp only [C.wTr, hb2, zero_div, add_zero, map_zero]
    simp only [← trans_bridge l L ι _ (hS.1 _ (Subtype.coe_prop _)).2]
    simp only [map_mul, map_add, map_sum, map_sub, PowerSeries.map_C, map_pow] at h
    have hr : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (PowerSeries.rescale α (F.pSeries L))
        = PowerSeries.rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L)) := by
      ext n
      simp [PowerSeries.coeff_rescale]
    rw [hr] at h
    simpa using h

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem end_not_dvd (d : ℕ) (hd : d % 4 = 3) (l : ℕ) [Fact l.Prime]
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) : ¬ l ∣ (d + 1) / 4 := by
  intro h
  apply hin
  refine ⟨1, ?_⟩
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h0 : ((d + 1 : ℕ) : ZMod l) = 0 := by
    rw [← h4, ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_left h 4
  push_cast at h0
  linear_combination h0

theorem end_unit (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : ¬ l ∣ n) (a : ℂ_[l]) (ha : ‖a‖ ≤ 1)
    (hq : a ^ 2 - a + (n : ℂ_[l]) = 0) : ‖a‖ = 1 := by
  have hnn : ‖(n : ℂ_[l])‖ = 1 := by
    simpa using kq_int_unit l (n : ℤ) (by exact_mod_cast hn)
  have hprod : a * (1 - a) = n := by linear_combination -hq
  have hb : ‖1 - a‖ ≤ 1 := by
    have e : 1 - a = 1 + -a := by ring
    rw [e]
    exact kq_add_le l _ _ 1 (by simp) (by rwa [norm_neg])
  refine le_antisymm ha ?_
  rw [← hnn, ← hprod, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb

theorem end_card (d : ℕ) (hd : d % 4 = 3) (L : PeriodPair) (hCM : HasCMBy d L) (S : Finset ℂ)
    (h0 : omegaK d ≠ 0) (hS : Formalism.L2.Th1.F.IsKerReps L (omegaK d) S) :
    S.card + 1 = (d + 1) / 4 := by
  have h1 := Formalism.L2.Th1.F.kerRepsCard L (omegaK d) S h0 hCM hS
  have h2 := (Formalism.L2.Th1.F.hasCMByStable d L hCM 0 1).2
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4' : (4 : ℝ) * (((d + 1) / 4 : ℕ) : ℝ) = (d : ℝ) + 1 := by exact_mod_cast h4
  have e : ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * omegaK d = omegaK d := by simp
  rw [e] at h2
  have h3 : ((S.card + 1 : ℕ) : ℝ) = (((d + 1) / 4 : ℕ) : ℝ) := by
    push_cast
    rw [h1, h2]
    push_cast
    linarith
  exact_mod_cast h3

theorem end_integral (d : ℕ) (L : PeriodPair) (hd : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (hl : 5 ≤ l) (hld : ¬ l ∣ d) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l))
    (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    IntegralPS ((uSer g2 g3).subst (C (ι (omegaK d)) * lgS g2 g3)) := by
  obtain ⟨L', hM, hCM'⟩ := good_lattice l L ι g2 g3 hg
  have hCM1 : HasCMBy d L' := hCM' d hCM
  have hl2 : l ≠ 2 := by omega
  have hquadC := omegaK_quad d hd
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι hquadC
    simpa using this
  have hln := end_not_dvd d hd l hin
  have hn0 : 0 < (d + 1) / 4 := by omega
  obtain ⟨ha1, -, -⟩ := kur_quad l d hd hl2 hld hin _ hquad
  have hau : ‖ι (omegaK d)‖ = 1 := end_unit l _ hln _ ha1 hquad
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have hα : omegaK d ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hau
    exact zero_ne_one hau
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L' (omegaK d) hα hCM1
  have hcard := end_card d hd L' hCM1 S hα hS
  obtain ⟨neg, hE⟩ := endo_curve l L' ι (omegaK d) S hα hCM1 hS
  rw [← hM.eq2, ← hM.eq3] at hE
  have htor : ∀ P : S, ‖ι (L'.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L'.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    obtain ⟨hP1, hP2⟩ := hS.1 P P.2
    refine tor_integral l hl2 L' ι g2 g3 hM _ hn0 hln P ?_ hP2
    have e : (((d + 1) / 4 : ℕ) : ℂ) * (P : ℂ) = omegaK d * (P : ℂ) - omegaK d * (omegaK d * (P : ℂ)) := by
      linear_combination (P : ℂ) * hquadC
    rw [e]
    exact sub_mem hP1 (hCM1 _ hP1)
  have hc : Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[l]) (Formalism.L2.Th1.A.shortW g2 g3) :=
    shortW_intModel g2 g3 hM.n2 hM.n3 h2
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := Formalism.L2.Th1.C.inv_mem_unitBall h2
  obtain ⟨hlp, hwp, hAx, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[l] (unitBall ℂ_[l]) _ hc
  have hDat := Formalism.L2.Th1.C.curveEndoR ℂ_[l] (unitBall ℂ_[l]) _ hc S neg _ _ (ι (omegaK d))
    (1 - ι (omegaK d)) hE (fun P => (htor P).1)
    (fun P => by
      change ‖ι (L'.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
      rw [norm_div, h2, div_one]
      exact (htor P).2)
    (by
      rw [Fintype.card_coe]
      have : ((S.card : ℂ_[l]) + 1) = (((d + 1) / 4 : ℕ) : ℂ_[l]) := by exact_mod_cast hcard
      rw [this]
      linear_combination -hquad)
    hau.le (Formalism.L2.Th1.C.inv_mem_unitBall hau)
    (by
      have : (Formalism.L2.Th1.A.shortW g2 g3).b₂ = 0 := by
        simp [Formalism.L2.Th1.A.shortW, WeierstrassCurve.b₂]
      rw [this]
      simp)
  have hEnd := Formalism.L2.Th1.C.endIntFromDatum ℂ_[l] (unitBall ℂ_[l]) _ _ _ _ _ S neg _ _ _ _ _
    hlp hwp hAx h2R hDat
  rw [lgS_eq_logSer, Formalism.L2.Th1.A.uSerEq]
  exact hEnd

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1
open scoped ComplexConjugate

theorem an_two_shift (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ) :
    F.sgStar L (z + ω₀ / 2)
      = -(Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2)) := by
  have h := F.sgStarQuasi L ω₀ (z - ω₀ / 2) h0
  have e1 : z - ω₀ / 2 + ω₀ = z + ω₀ / 2 := by ring
  have e2 : (Real.pi : ℂ) * F.herm L (z - ω₀ / 2) ω₀ + (Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2
      = (Real.pi : ℂ) * F.herm L z ω₀ := by
    unfold F.herm; ring
  have e3 : F.semiChar L ω₀ = -1 := by
    unfold F.semiChar; exact if_neg h1
  rw [e1, e2, e3] at h
  rw [h]; ring

theorem an_two_sq (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2) ^ 2
      = F.sgStar L z ^ 2 * F.sgStar L (ω₀ / 2) ^ 2
        * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) := by
  have h := F.sgStarAdd L z (ω₀ / 2) hz h1
  rw [an_two_shift L ω₀ h0 h1 z] at h
  linear_combination -h

theorem an_two_kap (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) * F.sgStar L (ω₀ / 2) ^ 4
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
  have hz : ω₀ / 4 ∉ L.lattice := by
    intro h
    apply h1
    have := L.lattice.add_mem h h
    have e : ω₀ / 4 + ω₀ / 4 = ω₀ / 2 := by ring
    rwa [e] at this
  have hzt : ω₀ / 4 + ω₀ / 2 ∉ L.lattice := by
    intro h
    apply hz
    have := L.lattice.sub_mem h0 h
    have e : ω₀ - (ω₀ / 4 + ω₀ / 2) = ω₀ / 4 := by ring
    rwa [e] at this
  have h2t : 2 * (ω₀ / 2) ∈ L.lattice := by
    have e : 2 * (ω₀ / 2) = ω₀ := by ring
    rwa [e]
  have hH := F.halfShift L (ω₀ / 2) (ω₀ / 4) h1 h2t hz hzt
  have hA := an_two_shift L ω₀ h0 h1 (ω₀ / 4)
  have hB1 := an_two_sq L ω₀ h0 h1 (ω₀ / 4) hz
  have hB2 := an_two_sq L ω₀ h0 h1 (ω₀ / 4 + ω₀ / 2) hzt
  have e1 : ω₀ / 4 + ω₀ / 2 - ω₀ / 2 = ω₀ / 4 := by ring
  have e2 : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4 + ω₀ / 2) ω₀)
      = Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀)
        * Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
    rw [← Complex.exp_add]; congr 1; unfold F.herm; ring
  rw [e1, e2, hA] at hB2
  have hs : F.sgStar L (ω₀ / 4) ≠ 0 := fun h => hz (((F.sgStarBasic L).2.2.1 _).1 h)
  have hE : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) ≠ 0 := Complex.exp_ne_zero _
  have hne : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) * F.sgStar L (ω₀ / 4) ^ 2 ≠ 0 :=
    mul_ne_zero hE (pow_ne_zero _ hs)
  apply mul_left_cancel₀ hne
  rw [← hH]
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) = E at *
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) = X at *
  generalize F.sgStar L (ω₀ / 4) = s at *
  generalize F.sgStar L (ω₀ / 4 - ω₀ / 2) = s' at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize L.weierstrassP (ω₀ / 4) - L.weierstrassP (ω₀ / 2) = a at *
  generalize L.weierstrassP (ω₀ / 4 + ω₀ / 2) - L.weierstrassP (ω₀ / 2) = b at *
  linear_combination (-1 : ℂ) * hB2 + (-(E * T ^ 2 * b)) * hB1

theorem an_two_odd (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (m : ℕ) :
    F.sgStar L (((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2)) ^ 2
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) ^ (2 * (m ^ 2 + m))
        * F.sgStar L (ω₀ / 2) ^ 2 := by
  have hm : (m : ℂ) * ω₀ ∈ L.lattice := by
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem h0 m
  have h := F.sgStarQuasi L ((m : ℂ) * ω₀) (ω₀ / 2) hm
  have e1 : ((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ / 2 + (m : ℂ) * ω₀ := by push_cast; ring
  have hchi : F.semiChar L ((m : ℂ) * ω₀) ^ 2 = 1 := by
    unfold F.semiChar; split_ifs <;> norm_num
  rw [e1, h, mul_pow, mul_pow, hchi, one_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2
  unfold F.herm
  simp only [map_mul, Complex.conj_natCast]
  push_cast
  ring

theorem an_two_card (L : PeriodPair) (n : ℕ) (hn : n ≠ 0) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) : S.card + 1 = n ^ 2 := by
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem hω n
  have h := F.kerRepsCard L (n : ℂ) S (by exact_mod_cast hn) hst hS
  have e : Complex.normSq (n : ℂ) = (n : ℝ) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.normSq_ofReal]; ring
  rw [e] at h
  exact_mod_cast h

theorem an_two (L : PeriodPair) (n : ℕ) (hn : Odd n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    ((n : ℂ) ^ 2 * ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P)) ^ 2
      = (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) ^ (n ^ 2 - 1) := by
  obtain ⟨m, rfl⟩ := hn
  have hn0 : 2 * m + 1 ≠ 0 := by omega
  have hst : F.MulStable L ((2 * m + 1 : ℕ) : ℂ) := by
    intro ω hω
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem hω _
  have hI := F.isogenySigma L ((2 * m + 1 : ℕ) : ℂ) S (by exact_mod_cast hn0) hst hS (ω₀ / 2) h1
  rw [an_two_card L _ hn0 S hS, an_two_odd L ω₀ h0 m, ← an_two_kap L ω₀ h0 h1] at hI
  have hT : F.sgStar L (ω₀ / 2) ≠ 0 := fun h => h1 (((F.sgStarBasic L).2.2.1 _).1 h)
  have ek : (2 * m + 1) ^ 2 - 1 = 4 * (m ^ 2 + m) := by
    have : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
    omega
  have ek2 : 2 * (2 * m + 1) ^ 2 = 8 * (m ^ 2 + m) + 2 := by ring
  rw [ek]
  rw [ek2] at hI
  clear ek ek2
  generalize m ^ 2 + m = k at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) = κ at *
  generalize ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P) = Q at *
  generalize ((2 * m + 1 : ℕ) : ℂ) = N at *
  have hT' : T ^ (8 * k + 2) ≠ 0 := pow_ne_zero _ hT
  have h3 : κ ^ (2 * k) = N ^ 2 * Q := by
    apply mul_left_cancel₀ hT'
    have : (κ * T ^ 4) ^ (2 * k) * T ^ 2 = T ^ (8 * k + 2) * κ ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, pow_add]
      have : 4 * (2 * k) = 8 * k := by ring
      rw [this]; ring
    rw [← this, hI]; ring
  rw [← h3, ← pow_mul]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

theorem kap_unit {K : Type} [NormedField K] [IsUltrametricDist K] (g2 g3 e : K) (h2 : ‖g2‖ ≤ 1)
    (h3 : ‖g3‖ ≤ 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (h22 : ‖(2 : K)‖ = 1)
    (he : 4 * e ^ 3 - g2 * e - g3 = 0) : ‖e‖ ≤ 1 ∧ ‖3 * e ^ 2 - g2 / 4‖ = 1 := by
  have hn1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have h4 : ‖(4 : K)‖ = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h22, one_mul]
  have h4ne : (4 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h4
    exact zero_ne_one h4
  have h3n : ‖(3 : K)‖ ≤ 1 := by simpa using hn1 3
  have h12n : ‖(12 : K)‖ ≤ 1 := by simpa using hn1 12
  have h15n : ‖(15 : K)‖ ≤ 1 := by simpa using hn1 15
  have h36n : ‖(36 : K)‖ ≤ 1 := by simpa using hn1 36
  have he1 : ‖e‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hE : 4 * e ^ 3 = g2 * e + g3 := by linear_combination he
    have hn : ‖(4 : K) * e ^ 3‖ = ‖e‖ ^ 3 := by rw [norm_mul, h4, one_mul, norm_pow]
    have hle : ‖g2 * e + g3‖ ≤ ‖e‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        nlinarith [norm_nonneg g2, norm_nonneg e]
      · linarith
    rw [← hE, hn] at hle
    have hsq : 1 < ‖e‖ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hsq (by linarith : (0 : ℝ) < ‖e‖)]
  refine ⟨he1, ?_⟩
  have hg3 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he
  have hid : g2 ^ 3 - 27 * g3 ^ 2 = (g2 - 12 * e ^ 2) * (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4) := by
    rw [hg3]
    ring
  have hk : 3 * e ^ 2 - g2 / 4 = -(g2 - 12 * e ^ 2) / 4 := by
    field_simp
    ring
  have hen : 0 ≤ ‖e‖ := norm_nonneg e
  have he2 : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ hen he1
  have he4 : ‖e‖ ^ 4 ≤ 1 := pow_le_one₀ hen he1
  have hQ : ‖g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) h2
      · rw [norm_neg, norm_mul, norm_mul, norm_pow]
        exact mul_le_one₀ (mul_le_one₀ h15n (by positivity) he2) (norm_nonneg _) h2
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ h36n (by positivity) he4
  have hP : ‖g2 - 12 * e ^ 2‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
    rw [norm_neg, norm_mul, norm_pow]
    exact mul_le_one₀ h12n (by positivity) he2
  have hP1 : 1 ≤ ‖g2 - 12 * e ^ 2‖ := by
    have := hΔ
    rw [hid, norm_mul] at this
    nlinarith [norm_nonneg (g2 - 12 * e ^ 2), norm_nonneg (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4)]
  rw [hk, norm_div, norm_neg, h4, div_one]
  exact le_antisymm hP hP1

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem half_cubic (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hM : LatModel l L ι g2 g3) :
    4 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 3 - g2 * ι (L.weierstrassP (L.ω₁ / 2)) - g3 = 0 := by
  have hd : L.derivWeierstrassP (L.ω₁ / 2) = 0 :=
    (F.pDerivZero L _ L.ω₁_div_two_notMem_lattice).2
      (by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact L.ω₁_mem_lattice)
  have h := L.derivWeierstrassP_sq _ L.ω₁_div_two_notMem_lattice
  rw [hd] at h
  have h' := congrArg ι h
  simp only [map_pow, map_mul, map_sub, map_zero, map_ofNat] at h'
  rw [hM.eq2, hM.eq3, ← h']
  norm_num

theorem half_prod_norm (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (S : Finset ℂ) (hS : F.IsKerReps L (l : ℂ) S)
    (hκ : ‖3 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 2 - g2 / 4‖ = 1) :
    ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L.weierstrassP (L.ω₁ / 2)) - ι (L.weierstrassP P)‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have h := congrArg ι (an_two L l (hlp.odd_of_ne_two hl) S hS L.ω₁ L.ω₁_mem_lattice
    L.ω₁_div_two_notMem_lattice)
  simp only [map_pow, map_mul, map_prod, map_sub, map_natCast, map_div₀, map_ofNat] at h
  rw [← hM.eq2] at h
  have hn := congrArg norm h
  rw [norm_pow, norm_pow _ (l ^ 2 - 1), hκ, one_pow, norm_mul, norm_prod] at hn
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 hn

theorem level_le (L : PeriodPair) (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3))‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := by omega
  obtain ⟨L', hM, -⟩ := good_lattice l L ι g2 g3 hg
  obtain ⟨-, -, h2, h3, hΔ, -⟩ := hg
  have h22 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd (l := l) (n := 2)
      (fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h))
    simpa using this
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hst : F.MulStable L' (l : ℂ) := fun ω hω => by
    have := L'.lattice.smul_mem (l : ℤ) hω
    simpa using this
  obtain ⟨S, hS⟩ := F.kerRepsExist L' (l : ℂ) hl0 hst
  have hcard : S.card + 1 = l ^ 2 := by
    have := F.kerRepsCard L' (l : ℂ) S hl0 hst hS
    rw [Complex.normSq_natCast] at this
    have h' : ((S.card + 1 : ℕ) : ℝ) = ((l ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [this]
      ring
    exact_mod_cast h'
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl2 L' ι g2 g3 hM l hlp.pos S hS
  obtain ⟨e', he'0, he'i, he'l⟩ := mulN_integral (curve_law g2 g3 h2 h3 h22) l
  have hee : e' = (uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3) :=
    mult_unique g2 g3 _ e' he'0 he'l
  rw [← hee] at hsq ⊢
  obtain ⟨hAi, hA0, -⟩ :=
    A.bridgeCurve ℂ_[l] (A.shortW g2 g3) (shortW_intModel g2 g3 h2 h3 h22)
  have hAi' : IntegralPS (A.xS (A.shortW g2 g3)) := (integralPS_iff_mv _).2 hAi
  have hGi := integral_of_sq_eq he'i he'0 hUi hU0 hsq
  have hb := gauss_bound S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ hGi
  obtain ⟨he1, hκ⟩ := kap_unit g2 g3 _ h2 h3 hΔ h22 (half_cubic l L' ι g2 g3 hM)
  have hp := half_prod_norm l hl2 L' ι g2 g3 hM S hS hκ
  have hle : ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L'.weierstrassP (L'.ω₁ / 2)) - ι (L'.weierstrassP P)‖
      ≤ ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, max 1 ‖ι (L'.weierstrassP P)‖ := by
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Finset.prod_le_prod (fun P _ => norm_nonneg _) fun P _ => ?_
    exact (norm_sub_le_max_Cl l _ _).trans (max_le_max he1 le_rfl)
  rw [hp] at hle
  obtain ⟨i, hi, hi1⟩ := unit_coeff_mul hUi hGi (by rw [hU0, norm_one]) _
    (gauss_unit S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ (le_antisymm hb hle))
  refine unit_coeff_of_sq he'i (l ^ 2) ⟨i + 2, by omega, ?_⟩
  rw [hsq, mul_assoc, coeff_X_pow_mul]
  exact hi1

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem integral_of_map_kur {l : ℕ} [Fact l.Prime] {f : PowerSeries (MaximalUnramifiedExtension l)}
    (h : IntegralPS (PowerSeries.map (MaximalUnramifiedExtension l).subtype f)) : IntegralPS f := fun n => by
  have := h n
  rw [PowerSeries.coeff_map] at this
  exact this

theorem cm3 : CM3 := by
  intro d L _hsq hd hCM l _ hl hld hin ι g2 g3 hg
  obtain ⟨hg2, hg3, hn2, hn3, -, -⟩ := id hg
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨σ, hσ⟩ := kurFrob l
  have hR := kur_resClosed l
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι (omegaK_quad d hd)
    simpa using this
  obtain ⟨-, ha1, ha', haσ⟩ := kur_quad l d hd (by omega) hld hin _ hquad
  have haσ' := haσ σ hσ
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := norm_natCast_of_coprime (K := MaximalUnramifiedExtension l) hσ.prime hσ.norm_l 2
      (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hlaw := curve_law (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ hn2 hn3 h2
  have hD : HD σ (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) _
      ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
        (C (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))
      ⟨ι (omegaK d), ha'⟩ :=
    { toLawD := hlaw
      A0 := mult_const _ _ _
      Aint := integral_of_map_kur (by
        rw [mult_map]
        exact end_integral d L hd hCM l hl hld hin ι g2 g3 hg)
      Alog := mult_log _ _ _
      a_ne := by
        rw [haσ']
        have : ‖((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 := by
          have e : ((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])
              = 1 - 2 * ι (omegaK d) := by
            push_cast; ring
          rw [e]; exact ha1
        exact this
      a_sq := by
        rw [haσ', map_sub, map_one, haσ']; ring }
  have he : IntegralPS ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)) := by
    obtain ⟨e', h0, hint, hlog⟩ := mulN_integral hlaw l
    rw [← mult_unique _ _ _ e' h0 hlog]
    exact hint
  have hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))‖ = 1 := by
    obtain ⟨i, hi, hu⟩ := level_le L l hl ι g2 g3 hg
    refine ⟨i, hi, ?_⟩
    have hm := mult_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ ((l : ℕ) : MaximalUnramifiedExtension l)
    have hl' : (MaximalUnramifiedExtension l).subtype ((l : ℕ) : MaximalUnramifiedExtension l) = ((l : ℕ) : ℂ_[l]) := map_natCast _ _
    rw [hl'] at hm
    have hc := congrArg (coeff i) hm
    rw [PowerSeries.coeff_map] at hc
    have : ‖(MaximalUnramifiedExtension l).subtype (coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)))‖ = 1 := by
      rw [hc]; exact hu
    exact this
  obtain ⟨c, hc, hT⟩ := hon_main hσ hD (mult_const _ _ _) he (mult_log _ _ _) hlev
  obtain ⟨ε, hε, hcε⟩ := lang_semilinear hσ hR c hc
  have hfin := fin_integral hσ (uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)
    (lgS_const _ _) (lgS_coeff_one _ _) (uSer_const _ _) (uSer_subst_lgS _ _) c ε hc hε hcε hT
  refine ⟨ε, ε.2, hε, fun n => ?_⟩
  have hm := lt_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ l (by omega) ε
  have hc' := congrArg (coeff n) hm
  rw [PowerSeries.coeff_map] at hc'
  have hc'' : coeff n ((uSer g2 g3).subst (C (ε : ℂ_[l]) * ltLog ℂ_[l] l))
      = (MaximalUnramifiedExtension l).subtype (coeff n ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
          (C ε * ltLog (MaximalUnramifiedExtension l) l))) := hc'.symm
  rw [hc'']
  exact ⟨SetLike.coe_mem _, hfin n⟩

end ReciprocityTheory.ChartRestriction.L1
end
end
