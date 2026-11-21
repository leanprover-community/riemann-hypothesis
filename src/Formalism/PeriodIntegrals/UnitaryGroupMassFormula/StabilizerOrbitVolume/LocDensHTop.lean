import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHI
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.Shared.HermitianInverse
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVDx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVol

section
noncomputable section

namespace PI.VolStabSW

namespace IdxLW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem index_maxIdeal :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)

def crdL : latSub b v a M →+ (Fin a × Fin M × Fin d → v.adicCompletionIntegers F) where
  toFun x q := ⟨(Algebra.TensorProduct.basis (Fv F v) b).repr ((x : Fin a → Fin M → Fv F v ⊗[F] E)
    q.1 q.2.1) q.2.2, x.2 q.1 q.2.1 q.2.2⟩
  map_zero' := by
    funext q
    apply Subtype.ext
    simp
  map_add' x y := by
    funext q
    apply Subtype.ext
    simp

theorem crdL_surj : Function.Surjective (crdL v b a M) := by
  intro c
  let x : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).repr.symm
      (Finsupp.equivFunOnFinite.symm fun k => (c (i, j, k) : Fv F v))
  have hx : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k = c (i, j, k) := by
    intro i j k
    simp [x]
  refine ⟨⟨x, fun i j k => by rw [hx]; exact (c (i, j, k)).2⟩, ?_⟩
  funext q
  apply Subtype.ext
  exact hx q.1 q.2.1 q.2.2

theorem crd_smul' (s : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (s • y) k =
      s * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
  simp [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem addSubgroupOf_eq :
    (lamF b v a M 0).addSubgroupOf (latSub b v a M) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin M × Fin d =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (crdL v b a M) := by
  have hv := unifV_val v
  have h0 := (unifV_spec v).1
  ext x
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, ReciprocityTheory.Aut.mem_maxIdeal_iff]
  constructor
  · intro hx q
    simp only [lamF, mem_smulSub, zero_add, pow_one] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    show Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
      ((x : Fin a → Fin M → Fv F v ⊗[F] E) q.1 q.2.1) q.2.2) < 1
    rw [← hpx]
    simp only [Pi.smul_apply]
    rw [crd_smul', map_mul, hv]
    have hp' : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr (p q.1 q.2.1) q.2.2) ≤ 1 := by
      have h := hp q.1 q.2.1 q.2.2
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    calc WithZero.exp (-1 : ℤ) * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
          (p q.1 q.2.1) q.2.2) ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; decide
  · intro hx
    simp only [lamF, mem_smulSub, zero_add, pow_one]
    refine ⟨(unifV v)⁻¹ • (x : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_⟩
    · intro i j k
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Pi.smul_apply]
      rw [crd_smul', map_mul, map_inv₀, hv]
      have := ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v (hx (i, j, k))
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
            ((x : Fin a → Fin M → Fv F v ⊗[F] E) i j) k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := by gcongr; exact this
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

end IdxLW

open IdxLW

theorem idxL_holds : IdxL := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ d b v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  unfold AddSubgroup.relIndex
  rw [addSubgroupOf_eq, AddSubgroup.index_comap_of_surjective _ (crdL_surj v b a M),
    AddSubgroup.index_pi]
  simp only [index_maxIdeal, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  subst hd
  ring_nf

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

namespace FiniteFieldCounting

theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    set P := ∏ j ∈ s, (1 + δ j)
    have hP : |P| ≤ 1 + |P - 1| := by
      have := abs_sub_abs_le_abs_sub P 1
      rw [abs_one] at this
      linarith
    have e : (1 + δ j) * P - 1 = (P - 1) + δ j * P := by ring
    rw [e]
    have h1 := abs_add_le (P - 1) (δ j * P)
    rw [abs_mul] at h1
    have hpow : (2 : ℝ) ^ (s.card + 1) = 2 * 2 ^ s.card := by ring
    rw [hpow]
    have h2 : |δ j| * |P| ≤ t * (1 + |P - 1|) := mul_le_mul (h j) hP (abs_nonneg _) ht0
    have h3 : 0 ≤ |P - 1| := abs_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h3]

theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  have := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
  zify [h1, ha]
  ring

theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
    have h2 : (a + 1) ^ 2 ≤ 2 * M * (a + 1) := by nlinarith
    have h3 : a ≤ M := by omega
    have h4 : 1 ≤ 2 * (M - a) := by omega
    zify [h1, h2, h3, h4]
    ring

theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hM : q ^ M ≠ 0 := pow_ne_zero _ hq
  have e1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  rw [Finset.prod_congr rfl fun i _ ↦ e1 i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, ← exp_id M a ha, pow_add]
  have h1 : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have e1 : ∀ j : Fin a, q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1) =
      q ^ (2 * (M - j) - 1) *
        (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
    intro j
    have : q ^ (2 * (M - j) - 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring
  rw [Finset.prod_congr rfl fun j _ ↦ e1 j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j ↦ 2 * (M - j) - 1) a, sum_exp M a ha]
  have h1 : q ^ (2 * M * a - a ^ 2) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hMi : q ^ M = q ^ (i : ℕ) * q ^ (M - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hq0
  have e : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    rw [hMi, inv_pow]
    field_simp
  rw [abs_neg, e, abs_of_nonneg (by positivity)]
  exact inv_pow_le q hq _ (by omega)

theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hexp : q ^ (2 * (M - j) - 1) = q ^ (M - j - 1) * q ^ (M - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (M - j - 1) ≠ 0 := pow_ne_zero _ hq0
  have e : |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| = (q⁻¹) ^ (M - j) := by
    rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hexp,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), inv_pow]
    field_simp
  rw [e]
  exact inv_pow_le q hq _ (by omega)

theorem swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl

theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (p := fun X ↦ ffGram (σ : K →+* K) J X = T)
    (q := fun Y ↦ ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e)
    { toFun := fun X r i ↦ e (X r i)
      invFun := fun Y r i ↦ e.symm (Y r i)
      left_inv := fun X ↦ by
        funext r i
        simp
      right_inv := fun Y ↦ by
        funext r i
        simp } ?_
  intro X
  have key : ∀ r s, ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s =
      e (ffGram (σ : K →+* K) J X r s) := by
    intro r s
    simp only [ffGram, ffH, map_sum, map_mul, Matrix.map_apply, swapR_apply, ← he]
    rfl
  constructor
  · intro h
    funext r s
    change ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s = _
    rw [key, h]
    rfl
  · intro h
    funext r s
    apply e.injective
    rw [← key]
    exact congrFun (congrFun h r) s

end FiniteFieldCounting

theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos (α := k)
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by positivity
  rcases hσ.2 with ⟨hK, hdeg, hne⟩ | ⟨e, he⟩
  · letI : Field K := hK.toField
    rw [hI k K σ hσ.1 hdeg hne h2 M a (by omega) J hJ hJd T hT hTd,
      FiniteFieldCounting.inert_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.inert_delta M a ha _ hq1)
  · have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have hd : e J.det = (J.map e).det := (e : K →+* k × k).map_det J
      rw [← hd]
      exact hJd.map e
    have hTd' : IsUnit (T.map e).det := by
      have hd : e T.det = (T.map e).det := (e : K →+* k × k).map_det T
      rw [← hd]
      exact hTd.map e
    rw [FiniteFieldCounting.card_transport σ e he J T, hS k M a (by omega) _ hJ' hJd' _ hT' hTd',
      FiniteFieldCounting.split_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.split_delta M a ha _ hq1)

theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabSW
end
end

section
namespace PI.VolStabSW

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabSW
end

section
noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix

section Mat

variable {A : Type} [CommRing A] (s : A →+* A)

theorem hform_mul_right {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l) =
      ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by
  calc Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l)
      = ∑ p, ∑ q, ∑ k, s (Y i p) * Jm p q * (C j k * Y k q) := by
        simp only [Formalism.UG.hform, Finset.mul_sum]
    _ = ∑ p, ∑ k, ∑ q, s (Y i p) * Jm p q * (C j k * Y k q) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ k, ∑ p, ∑ q, s (Y i p) * Jm p q * (C j k * Y k q) := Finset.sum_comm
    _ = ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by
        simp only [Formalism.UG.hform, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun q _ => by ring

theorem hform_mul_left {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j) =
      ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by
  calc Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j)
      = ∑ p, ∑ q, ∑ k, s (C i k) * s (Y k p) * Jm p q * Y j q := by
        simp only [Formalism.UG.hform, map_sum, map_mul, Finset.sum_mul]
    _ = ∑ p, ∑ k, ∑ q, s (C i k) * s (Y k p) * Jm p q * Y j q :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ k, ∑ p, ∑ q, s (C i k) * s (Y k p) * Jm p q * Y j q := Finset.sum_comm
    _ = ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by
        simp only [Formalism.UG.hform, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun q _ => by ring

theorem pol_solve {a : ℕ} (h πA : A) (hh : h + h = 1) (hsh : s h = h)
    (Γ Tm Tinv Sm E0 : Matrix (Fin a) (Fin a) A) (hΓ : Γ = Tm + πA • E0)
    (hTT : Tm * Tinv = 1) (hTs : (Tinv.map s)ᵀ * Tm = 1) (hS : ∀ i k, s (Sm k i) = Sm i k) :
    Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ =
      Sm + πA • (h • (E0 * Tinv * Sm + Sm * (Tinv.map s)ᵀ * E0)) := by
  set Ts := (Tinv.map s)ᵀ with hTsdef
  have hC1 : ((h • (Tinv * Sm))ᵀ)ᵀ = h • (Tinv * Sm) := transpose_transpose _
  have hC2 : ((h • (Tinv * Sm))ᵀ).map s = h • (Sm * Ts) := by
    ext i j
    simp only [hTsdef, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply,
      smul_eq_mul, map_mul, map_sum, hsh, hS]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  calc Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ
      = (Tm + πA • E0) * (h • (Tinv * Sm)) + h • (Sm * Ts) * (Tm + πA • E0) := by
        rw [hC1, hC2, hΓ]
    _ = h • ((Tm * Tinv) * Sm) + (πA * h) • (E0 * Tinv * Sm) +
          (h • (Sm * (Ts * Tm)) + (h * πA) • (Sm * Ts * E0)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_assoc, smul_smul]
        try module
    _ = (h + h) • Sm + πA • (h • (E0 * Tinv * Sm + Sm * Ts * E0)) := by
        rw [hTT, hTs, Matrix.one_mul, Matrix.mul_one]
        module
    _ = _ := by rw [hh, one_smul]

end Mat

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

def intA (z : Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F

variable {b v}

theorem intA_zero : intA b v 0 := fun k => by simp [zero_mem]

theorem intA_add {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z + w) :=
  fun k => by rw [map_add, Finsupp.add_apply]; exact add_mem (hz k) (hw k)

theorem intA_sum {ι : Type} (t : Finset ι) (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ t, intA b v (f i)) :
    intA b v (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using intA_zero
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact intA_add (hf x (Finset.mem_insert_self x t))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem intA_smul {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : intA b v z) : intA b v (c • z) :=
  fun k => by rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hc (hz k)

theorem intA_incl (e : E) (h : ∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ v.adicCompletionIntegers F) :
    intA b v (inclR (Fv F v) e) := fun m => by
  have := PositiveNearLattice.crd_incl b (Fv F v) e m
  simp only [PositiveNearLattice.crd] at this
  rw [this]
  exact h m

theorem incl_eq_tmul (e : E) : inclR (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e := rfl

theorem intA_mul (hg : ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈
      v.adicCompletionIntegers F)
    {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z * w) := by
  rw [PositiveNearLattice.eq_sum_crd b (Fv F v) z, PositiveNearLattice.eq_sum_crd b (Fv F v) w, Finset.sum_mul_sum]
  refine intA_sum _ _ fun i _ => intA_sum _ _ fun j _ => ?_
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← incl_eq_tmul]
  exact intA_smul (mul_mem (hz i) (hw j)) (intA_incl _ (hg i j))

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) :
    sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • z) = c • sigR (Fv F v) σ z := by
  rw [Algebra.smul_def, map_mul, sigR_algebraMap, ← Algebra.smul_def]

theorem intA_sig (σ : E →ₐ[F] E)
    (hg : ∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : intA b v z) : intA b v (sigR (Fv F v) σ z) := by
  rw [PositiveNearLattice.eq_sum_crd b (Fv F v) z, map_sum]
  refine intA_sum _ _ fun i _ => ?_
  rw [sigR_smul, ← incl_eq_tmul, sigR_incl]
  exact intA_smul (hz i) (intA_incl _ (hg i))

theorem aaInt (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  refine Filter.eventually_cofinite.2 (h.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  rw [not_le] at hv
  show 1 < v.valuation F x
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hv

def GoodV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) : Prop :=
  (∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ m, algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F)

theorem goodV_aa (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) :
    ∀ᶠ v in cofinite, GoodV b v σ J Tinv := by
  have k1 : ∀ᶠ v in cofinite, ∀ k l m : Fin d,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l =>
      Filter.eventually_all.2 fun m => aaInt _
  have k2 : ∀ᶠ v in cofinite, ∀ k m : Fin d,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => aaInt _
  have k3 : ∀ᶠ v in cofinite, ∀ (i j : Fin M) (m : Fin d),
      algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun m => aaInt _
  have k4 : ∀ᶠ v in cofinite, ∀ m : Fin d,
      algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun m => aaInt _
  have k5 : ∀ᶠ v in cofinite, ∀ (i j : Fin a) (m : Fin d),
      algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun m => aaInt _
  filter_upwards [k1, k2, k3, k4, k5] with v h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end Int

theorem map_smulSub' {K V X : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X]
    [Module K X] (D : V →+ X) (hDs : ∀ (t : K) w, D (t • w) = t • D w) (t : K)
    (L : AddSubgroup V) : (smulSub t L).map D = smulSub t (L.map D) := by
  ext z
  rw [AddSubgroup.mem_map, mem_smulSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hw
    exact ⟨D l, AddSubgroup.mem_map_of_mem _ hl, (hDs t l).symm⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hq
    exact ⟨t • l, (mem_smulSub _ _ _).2 ⟨l, hl, rfl⟩, hDs t l⟩

theorem hensAA_holds : HensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ := sigma_invol σ hCM.2.2.2
  set TE := gramE σ J X0 with hTE
  have hu : IsUnit TE.det := isUnit_iff_ne_zero.2 hdet
  filter_upwards [goodV_aa b σ J TE⁻¹] with v hg
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg
  intro y hy hyT
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  obtain ⟨hπ0, hπ, hπO⟩ := unifV_spec v
  set π := unifV v with hπdef
  set s := sigR (Fv F v) σ with hsdef
  set L := latSub b v a M with hLdef
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := fun w hw => LatFactsW.smul_mem_latSub b v hπO hw
  have hyL : ∀ i l, intA b v (y i l) := fun i l => hy i l

  let D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a :=
    { toFun := fun W => ⟨gramB (Fv F v) σ J y W, gramB_mem (Fv F v) σ hσ J hJ.1 y W⟩
      map_zero' := by
        apply Subtype.ext
        funext i j
        simp [gramB, hR, Formalism.UG.hform]
      map_add' := fun W W' => Subtype.ext (gramB_add_right (Fv F v) σ J y W W') }
  have hDv : ∀ W, (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J y W :=
    fun _ => rfl
  have hDc : Continuous D :=
    ((continuous_gramB (Fv F v) σ J).comp (Continuous.prodMk continuous_const continuous_id)).subtype_mk _
  have hDs : ∀ (t : Fv F v) W, D (t • W) = t • D W := by
    intro t W
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J y (t • W) i j = t • gramB (Fv F v) σ J y W i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]

  have hJi : ∀ i j, intA b v (JR (Fv F v) J i j) := fun i j => intA_incl _ (g3 i j)
  have hmul : ∀ {z w : Fv F v ⊗[F] E}, intA b v z → intA b v w → intA b v (z * w) :=
    fun hz hw => intA_mul g1 hz hw
  have hsig : ∀ {z : Fv F v ⊗[F] E}, intA b v z → intA b v (s z) := fun hz => intA_sig σ g2 hz
  have hRi : ∀ x z : Fin M → Fv F v ⊗[F] E, (∀ l, intA b v (x l)) → (∀ l, intA b v (z l)) →
      intA b v (hR (Fv F v) σ J x z) := by
    intro x z hx hz
    have e : hR (Fv F v) σ J x z = ∑ i, ∑ j, s (x i) * JR (Fv F v) J i j * z j := rfl
    rw [e]
    exact intA_sum _ _ fun i _ => intA_sum _ _ fun j _ =>
      hmul (hmul (hsig (hx i)) (hJi i j)) (hz j)
  have hgB : ∀ u w, u ∈ L → w ∈ L →
      (⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ.1 u w⟩ : HermR (Fv F v) σ a) ∈
        hermO b v σ a := by
    intro u w hu' hw' i j
    exact intA_add (hRi _ _ (hu' i) (hw' j)) (hRi _ _ (hw' i) (hu' j))
  have hgR : ∀ w, w ∈ L → gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a := by
    intro w hw' i j
    exact hRi _ _ (hw' i) (hw' j)
  have hOsm : ∀ {c : Fv F v}, c ∈ v.adicCompletionIntegers F → ∀ S ∈ hermO b v σ a,
      c • S ∈ hermO b v σ a := by
    intro c hc S hS i j
    exact intA_smul hc (hS i j)

  set Tm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE.map (inclR (Fv F v)) with hTm
  set Ti : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE⁻¹.map (inclR (Fv F v)) with hTi
  have hTT : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _)
      (map_one _)]
  have hTh : (TE.map (σ : E →+* E))ᵀ = TE := by
    ext i j
    exact hT i j
  have hE1 : (TE⁻¹.map (σ : E →+* E))ᵀ * TE = 1 :=
    Formalism.MassFormulaShared.inverseAdjoint_mul (σ : E →+* E) TE hTh hu
  have hTs : (Ti.map s)ᵀ * Tm = 1 := by
    have e : (Ti.map s)ᵀ = ((TE⁻¹.map (σ : E →+* E))ᵀ).map (inclR (Fv F v)) := by
      ext i j
      simp [hTi, hsdef, sigR_incl]
    rw [e, hTm, ← Matrix.map_mul, hE1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTii : ∀ i j, intA b v (Ti i j) := fun i j => intA_incl _ (g5 i j)

  set h : Fv F v ⊗[F] E := inclR (Fv F v) (1 / 2 : E) with hhdef
  have hh : h + h = 1 := by rw [hhdef, ← map_add, add_halves, map_one]
  have hsh : s h = h := by
    rw [hsdef, hhdef, sigR_incl]
    congr 1
    rw [map_div₀, map_one, map_ofNat]
  have hhi : intA b v h := intA_incl _ g4

  have hyT' : gramH (Fv F v) σ hσ J hJ.1 y - hermOf (Fv F v) σ TE hT ∈ smulSub π (hermO b v σ a) := by
    have := hyT
    simp only [hF, zero_add, pow_one] at this
    exact this
  obtain ⟨E0h, hE0, hE0eq⟩ := (mem_smulSub _ _ _).1 hyT'
  set πA : Fv F v ⊗[F] E := algebraMap (Fv F v) (Fv F v ⊗[F] E) π with hπA
  have hΓ : gramR (Fv F v) σ J y = Tm + πA • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    have e := congrArg Subtype.val hE0eq
    have e2 : π • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramR (Fv F v) σ J y - Tm := e
    rw [hπA, algebraMap_smul, e2]
    abel

  have hbase : ∀ S ∈ hermO b v σ a, ∃ l ∈ L, S - D l ∈ smulSub π (hermO b v σ a) := by
    intro S hS
    set Sm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := S.1 with hSm
    have hSh : ∀ i k, s (Sm k i) = Sm i k := fun i k => S.2 i k
    set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := (h • (Ti * Sm))ᵀ with hC
    set W : Fin a → Fin M → Fv F v ⊗[F] E := fun j l => ∑ k, C j k * y k l with hW
    have hCi : ∀ j k, intA b v (C j k) := by
      intro j k
      simp only [hC, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
      exact hmul hhi (intA_sum _ _ fun m _ => hmul (hTii k m) (hS m j))
    have hWL : W ∈ L := fun j l => intA_sum _ _ fun k _ => hmul (hCi j k) (hyL k l)
    have hgW : gramB (Fv F v) σ J y W = gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y := by
      ext i j
      simp only [gramB, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      rw [show hR (Fv F v) σ J (y i) (W j) = ∑ k, hR (Fv F v) σ J (y i) (y k) * C j k from
          hform_mul_right s (JR (Fv F v) J) y C i j,
        show hR (Fv F v) σ J (W i) (y j) = ∑ k, s (C i k) * hR (Fv F v) σ J (y k) (y j) from
          hform_mul_left s (JR (Fv F v) J) y C i j]
      rfl
    have hsol := pol_solve s h πA hh hsh (gramR (Fv F v) σ J y) Tm Ti Sm E0h hΓ hTT hTs hSh
    set R : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
      h • ((E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * Ti * Sm + Sm * (Ti.map s)ᵀ * E0h)
      with hRdef
    have hRi' : ∀ i j, intA b v (R i j) := by
      intro i j
      simp only [hRdef, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, smul_eq_mul]
      refine hmul hhi (intA_add (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hE0 i m) (hTii m k)) (hS k j)) (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hS i m) (hsig (hTii k m))) (hE0 k j)))
    have hsol' : gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y = Sm + πA • R := hsol
    have hDW : (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = Sm + π • R := by
      rw [hDv, hgW, hsol', hπA, algebraMap_smul]
    set Rh : HermR (Fv F v) σ a := π⁻¹ • (D W - S) with hRh
    have hRhv : (Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = R := by
      show π⁻¹ • ((D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) - Sm) = R
      rw [hDW, add_sub_cancel_left, inv_smul_smul₀ hπ0]
    have hRhO : Rh ∈ hermO b v σ a := by
      intro i j
      show intA b v ((Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j)
      rw [hRhv]
      exact hRi' i j
    refine ⟨W, hWL, (mem_smulSub _ _ _).2 ⟨-Rh, (hermO b v σ a).neg_mem hRhO, ?_⟩⟩
    rw [hRh, smul_neg, smul_inv_smul₀ hπ0, neg_sub]
  have hreach := reach_of_approx π hπ L hLc hπL D hDc hDs (hermO b v σ a)
    (LatFactsW.isCompact_hermO b v σ a) hbase
  have hDL : L.map D = hermO b v σ a := by
    refine le_antisymm ?_ fun p hp => ?_
    · rintro _ ⟨W, hW, rfl⟩
      exact hgB y W hy hW
    · obtain ⟨l, hl, e⟩ := hreach p hp
      exact AddSubgroup.mem_map.2 ⟨l, hl, e⟩
  refine ⟨D, fun n => ?_, fun n Z hZ W hW => ?_⟩
  · rw [lamF, hF, map_smulSub' D hDs, hDL]
  · obtain ⟨z, hz, rfl⟩ := (mem_smulSub _ _ _).1 hZ
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub _ _ _).1 hW
    rw [hF, mem_smulSub]
    have hB : (⟨gramB (Fv F v) σ J z w, gramB_mem (Fv F v) σ hσ J hJ.1 z w⟩ :
        HermR (Fv F v) σ a) ∈ hermO b v σ a := hgB z w hz hw
    have hG : π ^ n • gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a :=
      hOsm (pow_mem hπO n) _ (hgR w hw)
    refine ⟨_, (hermO b v σ a).add_mem hB hG, ?_⟩
    apply Subtype.ext
    show π ^ (n + 1 + 1) • (gramB (Fv F v) σ J z w + π ^ n • gramR (Fv F v) σ J w) =
      gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w)
    have e2 : gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w) =
        gramB (Fv F v) σ J (unifV v ^ (0 + 1) • z) (unifV v ^ (n + 1) • w) +
          gramR (Fv F v) σ J (unifV v ^ (n + 1) • w) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, gramB, gramR, Pi.add_apply, hR_add_left,
        hR_add_right]
      ring
    have gBs : ∀ (t t' : Fv F v) (u u' : Fin a → Fin M → Fv F v ⊗[F] E),
        gramB (Fv F v) σ J (t • u) (t' • u') = (t * t') • gramB (Fv F v) σ J u u' := by
      intro t t' u u'
      ext i j
      simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    have gRs : ∀ (t : Fv F v) (u : Fin a → Fin M → Fv F v ⊗[F] E),
        gramR (Fv F v) σ J (t • u) = (t * t) • gramR (Fv F v) σ J u := by
      intro t u
      ext i j
      simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    rw [e2, gBs, gRs, ← hπdef]
    module

end PI.VolStabSW
end
end

section
namespace PI.VolStabSW

theorem densAA_of_open (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) : DensAA :=
  densAA_of fibLat_holds fFCount_holds
    (resAA_of hV latFacts_holds hH (idxAA_of idxL_holds hI) hC)

end PI.VolStabSW
end
