import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues : ∀ (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → GlobalTheory.LGrp.IsIrrSmooth π → IsSmooth ρ → ∀ x ∈ fixed π K, x ≠ 0 → ∀ y ∈ fixed ρ K, y ≠ 0 → (∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) → GlobalTheory.LGrp.IsSubquot π ρ := by
  first | exact @GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | exact GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | (intros; apply GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues <;> assumption)
end

section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π → FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  first | exact @GlobalTheory.LFun.HeckeScalar.exists_scalar | exact GlobalTheory.LFun.HeckeScalar.exists_scalar | (intros; apply GlobalTheory.LFun.HeckeScalar.exists_scalar <;> assumption)
end

section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  first | exact @GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU | exact GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU | (intros; apply GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU <;> assumption)
end

section
section
namespace GlobalTheory.LaurentFinite

open AddMonoidAlgebra

def cut (j n : ℤ) : ℤ := if j ≤ |n| then Int.sign n else 0

theorem abs_cut_le (j n : ℤ) : |cut j n| ≤ 1 := by
  unfold cut
  split_ifs
  · rcases lt_trichotomy n 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [h]
    · simp [Int.sign_eq_one_of_pos h]
  · simp

theorem pointwise_lt (j n k : ℤ) (hj : 2 ≤ j) (hn : |n| ≠ j - 1) (hk : |k| ≤ 1)
    (hne : k ≠ cut j n) :
    (2 * j - 2) * (|cut j n| - |k|) < n ^ 2 - (n - cut j n + k) ^ 2 := by
  have hk' : k = -1 ∨ k = 0 ∨ k = 1 := by
    rw [abs_le] at hk; omega
  unfold cut at *
  split_ifs at * with h
  · rcases lt_trichotomy n 0 with h0 | h0 | h0
    · rw [Int.sign_eq_neg_one_of_neg h0] at *
      rw [abs_of_neg h0] at h hn
      rcases hk' with rfl | rfl | rfl
      · exact absurd rfl hne
      · norm_num; nlinarith
      · norm_num; nlinarith
    · subst h0; simp at h; omega
    · rw [Int.sign_eq_one_of_pos h0] at *
      rw [abs_of_pos h0] at h hn
      rcases hk' with rfl | rfl | rfl
      · norm_num; nlinarith
      · norm_num; nlinarith
      · exact absurd rfl hne
  · have h2 : |n| ≤ j - 2 := by omega
    rw [abs_le] at h2
    rcases hk' with rfl | rfl | rfl
    · norm_num; nlinarith [h2.1, h2.2]
    · exact absurd rfl hne
    · norm_num; nlinarith [h2.1, h2.2]

theorem sum_sq_lt {m : ℕ} (j : ℤ) (ν κ : Fin m → ℤ) (hj : 2 ≤ j) (hν : ∀ i, |ν i| ≠ j - 1)
    (hκ : ∀ i, |κ i| ≤ 1) (hs : ∑ i, |κ i| ≤ ∑ i, |cut j (ν i)|)
    (hne : κ ≠ fun i => cut j (ν i)) :
    ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 < ∑ i, ν i ^ 2 := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hne
  have h1 : ∑ i, (2 * j - 2) * (|cut j (ν i)| - |κ i|)
      < ∑ i, (ν i ^ 2 - (ν i - cut j (ν i) + κ i) ^ 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases h : κ i = cut j (ν i)
      · rw [h]; simp
      · exact (pointwise_lt j _ _ hj (hν i) (hκ i) h).le
    · exact ⟨i0, Finset.mem_univ _, pointwise_lt j _ _ hj (hν i0) (hκ i0) hi0⟩
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
  have : 0 ≤ (2 * j - 2) * (∑ i, |cut j (ν i)| - ∑ i, |κ i|) :=
    mul_nonneg (by omega) (by omega)
  omega

theorem exists_gap {m : ℕ} (ν : Fin m → ℤ) (i0 : Fin m) (h : (m : ℤ) < |ν i0|) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≤ |ν i0| ∧ ∀ i, |ν i| ≠ j - 1 := by
  have hcard : ((Finset.univ.erase i0).image fun i => |ν i|).card < (Finset.Icc (1 : ℤ) m).card := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    have := i0.pos
    simp
    omega
  obtain ⟨t, ht, ht'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_Icc] at ht
  refine ⟨t + 1, by omega, by omega, fun i hi => ?_⟩
  by_cases h0 : i = i0
  · subst h0; omega
  · exact ht' (Finset.mem_image.mpr ⟨i, by simp [h0], by omega⟩)

theorem finite_of_triangular (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ)))
    (hB : ∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧
      ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) :
    Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  classical
  set S : Finset (AddMonoidAlgebra ℂ (Fin m → ℤ)) :=
    (Fintype.piFinset fun _ : Fin m => Finset.Icc (-(m : ℤ)) m).image fun ν => single ν 1 with hS
  set N : Submodule B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := Submodule.span B (S : Set _) with hN
  have hsm : ∀ (ν : Fin m → ℤ) (c : ℂ), single ν 1 ∈ N → single ν c ∈ N := by
    intro ν c h
    have := N.smul_of_tower_mem c h
    rwa [smul_single', mul_one] at this
  have key : ∀ (n : ℕ) (ν : Fin m → ℤ), ∑ i, ν i ^ 2 < n → single ν (1 : ℂ) ∈ N := by
    intro n
    induction n with
    | zero =>
      intro ν h
      have : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      simp at h
      omega
    | succ n ih =>
      intro ν h
      by_cases hb : ∀ i, |ν i| ≤ m
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ν, ?_, rfl⟩)
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_Icc.mpr (abs_le.mp (hb i))
      · push Not at hb
        obtain ⟨i0, hi0⟩ := hb
        obtain ⟨j, hj, hj0, hν⟩ := exists_gap ν i0 hi0
        set ε : Fin m → ℤ := fun i => cut j (ν i) with hε
        obtain ⟨s, hsB, hs0, hs⟩ := hB ε fun i => abs_cut_le _ _
        have step : ∀ κ : Fin m → ℤ, (∀ i, |κ i| ≤ 1) → ∑ i, |κ i| ≤ ∑ i, |ε i| → κ ≠ ε →
            single (κ + (ν - ε)) (1 : ℂ) ∈ N := by
          intro κ h1 h2 h3
          apply ih
          have := sum_sq_lt j ν κ hj hν h1 h2 h3
          have e : ∑ i, (κ + (ν - ε)) i ^ 2 = ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 :=
            Finset.sum_congr rfl fun i _ => by simp [hε, add_comm]
          push_cast at h
          omega
        have h0 : single (ν - ε) (1 : ℂ) ∈ N := by
          have := step 0 (by simp) (by simpa using Finset.sum_nonneg fun i _ => abs_nonneg (ε i)) (by
            intro h0
            have h1 : ε i0 = 0 := by rw [← h0]; rfl
            simp only [hε, cut, hj0, if_true, Int.sign_eq_zero_iff_zero] at h1
            rw [h1] at hj0
            simp at hj0
            omega)
          rwa [zero_add] at this
        have h1 : s * single (ν - ε) (1 : ℂ) ∈ N := N.smul_mem ⟨s, hsB⟩ h0
        have h2 : s * single (ν - ε) (1 : ℂ)
            = ∑ κ ∈ s.coeff.support, single (κ + (ν - ε)) (s.coeff κ) := by
          conv_lhs => rw [← sum_coeff_single s, Finsupp.sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun κ _ => by rw [single_mul_single, mul_one]
        rw [h2, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.mpr hs0)] at h1
        have h3 : ∑ κ ∈ s.coeff.support.erase ε, single (κ + (ν - ε)) (s.coeff κ) ∈ N := by
          refine N.sum_mem fun κ hκ => hsm _ _ ?_
          rw [Finset.mem_erase, Finsupp.mem_support_iff] at hκ
          exact step κ (hs κ hκ.2).1 (hs κ hκ.2).2 hκ.1
        have h4 := N.smul_of_tower_mem (s.coeff ε)⁻¹ ((N.add_mem_iff_left h3).mp h1)
        rwa [smul_single', inv_mul_cancel₀ hs0, add_sub_cancel] at h4
  refine Module.Finite.of_fg_top ⟨S, ?_⟩
  rw [eq_top_iff]
  intro x _
  change x ∈ N
  induction x using induction_linear with
  | zero => exact N.zero_mem
  | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)
  | single ν c =>
    refine hsm _ _ (key ((∑ i, ν i ^ 2).toNat + 1) ν ?_)
    push_cast
    omega

end GlobalTheory.LaurentFinite
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_finite_of_triangular_signed_indicators : ∀ (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ))), (∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧ ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) → Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  atlas_forward_decl GlobalTheory.LaurentFinite.finite_of_triangular
end

section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.SatCoef

open GlobalTheory.InertThetaCompare

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}

open Classical in

def cellSum (ϖ : L) (h : GU σ n → ℂ) (a : Fin (n / 2) → ℤ) : ℂ :=
  ∑ᶠ x : GU σ n ⧸ KU σ n, if Cell ϖ a x then h x.out else 0

theorem exists_of_cellSum {h : GU σ n → ℂ} {a : Fin (n / 2) → ℤ} (ha : cellSum ϖ h a ≠ 0) :
    ∃ x : GU σ n ⧸ KU σ n, h x.out ≠ 0 ∧ Cell ϖ a x := by
  classical
  by_contra hne
  push Not at hne
  refine ha (finsum_eq_zero_of_forall_eq_zero fun x => ?_)
  split_ifs with hx
  · by_contra h0
    exact hne x h0 hx
  · rfl

theorem finite_supp (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {x : GU σ n ⧸ KU σ n | h x.out ≠ 0}.Finite :=
  P.finite_support_cosets (P.isCommensurated_integral_unitary_of_unramified hU n) hh.2

theorem finite_cellSum (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {a | cellSum ϖ h a ≠ 0}.Finite := by
  refine ((finite_supp hU hh).biUnion (t := fun x => {a | Cell ϖ a x}) fun x _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro a ⟨u, hu, k, hk, e⟩ a' ⟨u', hu', k', hk', e'⟩
    exact P.fSatake_cell_unique hU (Nat.mul_div_le n 2) hu hu' hk hk' (e.symm.trans e')
  · intro a ha
    obtain ⟨x, hx⟩ := exists_of_cellSum ha
    exact Set.mem_biUnion hx.1 hx.2

theorem cellSum_dosetInd (hU : IsUnramInv ϖ σ q) (t : GU σ n) (ε : Fin (n / 2) → ℤ)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε) :
    cellSum ϖ (dosetInd ℂ (KU σ n) t) ε ≠ 0 := by
  classical
  have hf : {x : GU σ n ⧸ KU σ n | Cell ϖ ε x ∧ dosetInd ℂ (KU σ n) t x.out ≠ 0}.Finite :=
    (finite_supp hU (Final.DosetIndMem _ _ ℂ t)).subset fun x hx => hx.2
  have key : ∀ x : GU σ n ⧸ KU σ n, ∀ [Decidable (Cell ϖ ε x)],
      (if Cell ϖ ε x then dosetInd ℂ (KU σ n) t x.out else 0) = if x ∈ hf.toFinset then 1 else 0 := by
    intro x _
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_cases h1 : Cell ϖ ε x
    · by_cases h2 : dosetInd ℂ (KU σ n) t x.out = 0
      · simp [h1, h2]
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
        unfold dosetInd at h2 ⊢
        exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero h2) _
    · simp [h1]
  unfold cellSum
  rw [finsum_congr fun x => @key x _, finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (fun x hx => by
    by_contra h
    exact hx (if_neg h)), Finset.sum_congr rfl fun x hx => if_pos hx]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
  refine Finset.ne_empty_of_mem (a := (QuotientGroup.mk t : GU σ n ⧸ KU σ n)) ?_
  rw [Set.Finite.mem_toFinset]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ n) t
  refine ⟨⟨1, ⟨P.fSatake_borel_one, fun i => by simp⟩, k, k.2, ?_⟩, ?_⟩
  · rw [hk]
    simp only [Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  · rw [hk]
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k.1, k.2, by rw [one_mul]⟩ :
      t * k.1 ∈ DoubleCoset.doubleCoset t (KU σ n : Set (GU σ n)) (KU σ n : Set (GU σ n)))]
    exact one_ne_zero

theorem satU_laurent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  intro L _ _ ϖ σ q n hU h hh
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let f : (Fin (n / 2) → ℤ) → ℂ := fun a =>
    (∏ i : Fin (n / 2), (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * cellSum ϖ h a
  have hf : (Function.support f).Finite := (finite_cellSum hU hh).subset fun a ha => right_ne_zero_of_mul ha
  refine ⟨Finsupp.ofSupportFinite f hf, fun α => ?_, fun κ hκ => ?_, fun t ε ht e => ?_⟩
  · have e : SatU ϖ q h α = ∑ᶠ a, f a * ∏ i, α i ^ a i := by
      unfold SatU
      refine finsum_congr fun a => ?_
      rw [Finset.prod_mul_distrib, mul_comm (∏ i, α i ^ a i), mul_right_comm]
      rfl
    rw [e, Finsupp.sum]
    exact finsum_eq_sum_of_support_subset _ fun a ha =>
      Finset.mem_coe.2 (Finsupp.mem_support_iff.2 (left_ne_zero_of_mul ha))
  · obtain ⟨x, h1, h2⟩ := exists_of_cellSum (right_ne_zero_of_mul (show f κ ≠ 0 from hκ))
    exact ⟨x.out, h1, h2⟩
  · subst e
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq) (cellSum_dosetInd hU t ε ht)

end GlobalTheory.LFun.SatCoef

end
end

section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  first | exact @GlobalTheory.LFun.SatCoef.satU_laurent | exact GlobalTheory.LFun.SatCoef.satU_laurent | (intros; apply GlobalTheory.LFun.SatCoef.satU_laurent <;> assumption)
end

section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.InertThetaCompare

namespace GlobalTheory.LFun.CellBound

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

private theorem det_mem_foundation {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m L)
    (h : ∀ i j, M i j ∈ intL L) : M.det ∈ intL L := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

private theorem valuation_zpow_uniformizer' {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem valuation_prod_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {ι : Type}
    (s : Finset ι) (m : ι → ℤ) :
    Valued.v (∏ i ∈ s, ϖ ^ m i) = WithZero.exp (-∑ i ∈ s, m i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j s hj ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj, map_mul, ih, valuation_zpow_uniformizer' hϖ, ← WithZero.exp_add]
    congr 1
    ring

theorem minor_le {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {a μ : Fin n → ℤ}
    {b k₁ k₂ : Matrix (Fin n) (Fin n) L} (hb : b.BlockTriangular id) (hd : ∀ i, b i i = ϖ ^ a i)
    (h₁ : ∀ i j, k₁ i j ∈ intL L) (h₂ : ∀ i j, k₂ i j ∈ intL L)
    (e : b = k₁ * Matrix.diagonal (fun i => ϖ ^ μ i) * k₂) (I : Finset (Fin n)) (c : ℤ)
    (hc : ∀ S : Finset (Fin n), S.card = I.card → c ≤ ∑ i ∈ S, μ i) :
    c ≤ ∑ i ∈ I, a i := by
  classical
  have hint : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  let A : Matrix I (Fin n) L := fun i s => k₁ i s * ϖ ^ μ s
  let B : Matrix (Fin n) I L := fun s j => k₂ s j
  have hM : b.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n)) = A * B := by
    ext i j
    rw [Matrix.mul_apply]
    simp [A, B, e, Matrix.mul_apply, Matrix.diagonal_apply]
  have hdet : (b.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).det =
      ∏ i : I, ϖ ^ a i := by
    have ht : (b.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).BlockTriangular id :=
      fun i j hij => hb (show (j : Fin n) < i from hij)
    rw [Matrix.det_of_upperTriangular ht]
    simp [hd]
  have hexp : (A * B).det = ∑ f : I → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    simp only [Matrix.det_apply, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
      Finset.smul_sum, Finset.mul_sum, Matrix.submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
    ring
  have hterm : ∀ f : I → Fin n,
      Valued.v ((∏ i, B (f i) i) * (A.submatrix id f).det) ≤ WithZero.exp (-c) := by
    intro f
    by_cases hf : Function.Injective f
    · have hA : A.submatrix id f = k₁.submatrix (fun i : I => (i : Fin n)) f *
          Matrix.diagonal (fun j => ϖ ^ μ (f j)) := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, id]
        rfl
      rw [hA, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_mul, valuation_prod_zpow_uniformizer hϖ]
      have h1 : Valued.v (∏ i, B (f i) i) ≤ 1 := (hint _).mp (prod_mem fun i _ => h₂ _ _)
      have h2 : Valued.v (k₁.submatrix (fun i : I => (i : Fin n)) f).det ≤ 1 :=
        (hint _).mp (det_mem_foundation _ fun i j => h₁ _ _)
      have h3 : c ≤ ∑ i, μ (f i) := by
        have := hc (Finset.univ.image f)
          (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe])
        rwa [Finset.sum_image (fun x _ y _ h => hf h)] at this
      calc Valued.v (∏ i, B (f i) i) *
            (Valued.v (k₁.submatrix (fun i : I => (i : Fin n)) f).det * WithZero.exp (-∑ i, μ (f i)))
          ≤ 1 * (1 * WithZero.exp (-∑ i, μ (f i))) := mul_le_mul' h1 (mul_le_mul' h2 le_rfl)
        _ ≤ WithZero.exp (-c) := by rw [one_mul, one_mul, WithZero.exp_le_exp]; omega
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        simp only [Function.Injective, not_forall] at hf
        obtain ⟨i, j, h, hne⟩ := hf
        exact ⟨i, j, h, hne⟩
      rw [Matrix.det_zero_of_column_eq hne (fun r => by simp [hij]), mul_zero, map_zero]
      exact zero_le'
  have hle : Valued.v (∏ i : I, ϖ ^ a i) ≤ WithZero.exp (-c) := by
    rw [← hdet, hM, hexp]
    exact Valuation.map_sum_le _ fun f _ => hterm f
  rw [valuation_prod_zpow_uniformizer hϖ, WithZero.exp_le_exp] at hle
  have : ∑ i : I, a i = ∑ i ∈ I, a i := Finset.sum_coe_sort I a
  omega

end Local

theorem tExp_lo {n : ℕ} (a : Fin (n / 2) → ℤ) (i : Fin (n / 2)) :
    tExp n (n / 2) a ⟨i.1, by omega⟩ = a i := by
  unfold tExp
  split_ifs with h h'
  · rfl
  · exact absurd i.2 h
  · exact absurd i.2 h

theorem tExp_hi {n : ℕ} (a : Fin (n / 2) → ℤ) (i : Fin (n / 2)) :
    tExp n (n / 2) a ⟨n - 1 - i.1, by omega⟩ = -a i := by
  have hi := i.2
  have e : n - 1 - (n - 1 - i.1) = i.1 := by omega
  unfold tExp
  split_ifs with h h'
  · exfalso
    have h2 : n - 1 - i.1 < n / 2 := h
    omega
  · rw [neg_inj]
    congr 1
    apply Fin.ext
    exact e
  · exfalso
    exact h' ⟨by show n - n / 2 ≤ n - 1 - i.1; omega, by show n - 1 - (n - 1 - i.1) < n / 2; omega⟩

theorem sum_min_tExp {n : ℕ} (a : Fin (n / 2) → ℤ) :
    ∑ j, min (tExp n (n / 2) a j) 0 = -∑ i, |a i| := by
  set f : Fin n → ℤ := fun j => min (tExp n (n / 2) a j) 0 with hf
  let lo : Fin (n / 2) → Fin n := fun i => ⟨i.1, by omega⟩
  let hi : Fin (n / 2) → Fin n := fun i => ⟨n - 1 - i.1, by omega⟩
  have hlo : Function.Injective lo := fun i i' h => Fin.ext (by simpa [lo] using congrArg Fin.val h)
  have hhi : Function.Injective hi := by
    intro i i' h
    have := congrArg Fin.val h
    simp only [hi] at this
    have := i.2; have := i'.2
    exact Fin.ext (by omega)
  have hdisj : Disjoint (Finset.univ.image lo) (Finset.univ.image hi) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨i', -, h⟩ := Finset.mem_image.mp hj'
    have := congrArg Fin.val h
    simp only [lo, hi] at this
    have := i.2; have := i'.2
    omega
  have hzero : ∀ j ∉ Finset.univ.image lo ∪ Finset.univ.image hi, f j = 0 := by
    intro j hj
    rw [Finset.mem_union, not_or] at hj
    simp only [hf]
    unfold tExp
    split_ifs with h1 h2
    · exact (hj.1 (Finset.mem_image.mpr ⟨⟨j.1, h1⟩, Finset.mem_univ _, rfl⟩)).elim
    · exfalso
      apply hj.2
      refine Finset.mem_image.mpr ⟨⟨n - 1 - j.1, h2.2⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext (by show n - 1 - (n - 1 - j.1) = j.1; have := j.2; omega)
    · simp
  rw [← Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hzero j hj),
    Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => hlo h),
    Finset.sum_image (fun x _ y _ h => hhi h), ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hf, lo, hi, tExp_lo, tExp_hi]
  rcases le_total (a i) 0 with h | h
  · rw [abs_of_nonpos h, min_eq_left h, min_eq_right (by omega)]; ring
  · rw [abs_of_nonneg h, min_eq_right h, min_eq_left (by omega)]; ring

theorem neg_one_le_tExp {n : ℕ} {a : Fin (n / 2) → ℤ} (h : ∀ i, |a i| ≤ 1) (j : Fin n) :
    -1 ≤ tExp n (n / 2) a j := by
  unfold tExp
  split_ifs with h1 h2
  · exact (abs_le.mp (h _)).1
  · have := (abs_le.mp (h ⟨n - 1 - j.1, h2.2⟩)).2
    omega
  · norm_num

private theorem entries_mem_intL_of_mem_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    {σ : L →+* L} {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) (i j : Fin n) :
    ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf] at hk
  unfold intPts at hk
  obtain ⟨g, hg⟩ := (Subgroup.mem_inf.mp hk).2
  rw [← hg]
  unfold bc
  exact ((g : Matrix (Fin n) (Fin n) (intL L)) i j).2

private theorem tMat_eq_diagonal_pow_tExp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (n : ℕ) (a : Fin (n / 2) → ℤ) :
    tMat ϖ n (n / 2) a = Matrix.diagonal (fun j => ϖ ^ tExp n (n / 2) a j) := by
  unfold tMat tExp
  congr 1
  funext j
  split_ifs <;> simp

theorem cell_bound : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (ε κ : Fin (n / 2) → ℤ) (u k k₁ k₂ : GU σ n), (∀ i, |ε i| ≤ 1) → IsUnipU u → k ∈ KU σ n → k₁ ∈ KU σ n → k₂ ∈ KU σ n → tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tMat ϖ n (n / 2) ε * ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i| := by
  intro L _ _ ϖ σ q n hU ε κ u k k₁ k₂ hε hu hk hk₁ hk₂ e
  classical
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  set U := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hU'
  set K := ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hK
  set K₁ := ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hK₁
  set K₂ := ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hK₂
  set Ki := (((k⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hKi
  have hKK : K * Ki = 1 := by
    show ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((k : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1
    exact Units.mul_inv _
  have hint₂ : ∀ i j, (K₂ * Ki) i j ∈ intL L := fun i j =>
    entries_mem_intL_of_mem_KU (mul_mem hk₂ (inv_mem hk)) i j
  set b := tMat ϖ n (n / 2) κ * U with hbdef
  have hbe : b = K₁ * Matrix.diagonal (fun j => ϖ ^ tExp n (n / 2) ε j) * (K₂ * Ki) := by
    calc b = b * (K * Ki) := by rw [hKK, Matrix.mul_one]
      _ = (b * K) * Ki := (Matrix.mul_assoc b K Ki).symm
      _ = K₁ * tMat ϖ n (n / 2) ε * K₂ * Ki := by rw [e]
      _ = _ := by rw [tMat_eq_diagonal_pow_tExp, Matrix.mul_assoc]
  have hbT : b.BlockTriangular id := by
    intro i j hij
    rw [hbdef, tMat_eq_diagonal_pow_tExp, Matrix.diagonal_mul]
    exact mul_eq_zero_of_right _ (show U i j = 0 from hu.1 i j hij)
  have hbd : ∀ j, b j j = ϖ ^ tExp n (n / 2) κ j := by
    intro j
    rw [hbdef, tMat_eq_diagonal_pow_tExp, Matrix.diagonal_mul, show U j j = 1 from hu.2 j, mul_one]
  have key := fun I c hc => minor_le hϖ hbT hbd (fun i j => entries_mem_intL_of_mem_KU hk₁ i j) hint₂ hbe I c hc
  have hlow : ∀ j, -1 ≤ tExp n (n / 2) κ j := by
    intro j
    have := key {j} (-1) (by
      intro S hS
      obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp (by rw [hS, Finset.card_singleton])
      rw [Finset.sum_singleton]
      exact neg_one_le_tExp hε s)
    rwa [Finset.sum_singleton] at this
  refine ⟨fun i => abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · have := hlow ⟨i.1, by omega⟩
    rwa [tExp_lo] at this
  · have := hlow ⟨n - 1 - i.1, by omega⟩
    rw [tExp_hi] at this
    linarith
  · have hS : ∀ S : Finset (Fin n), -∑ i, |ε i| ≤ ∑ i ∈ S, tExp n (n / 2) ε i := by
      intro S
      rw [← sum_min_tExp, ← Finset.sum_sdiff (Finset.subset_univ S)]
      have h1 : ∑ i ∈ Finset.univ \ S, min (tExp n (n / 2) ε i) 0 ≤ 0 :=
        Finset.sum_nonpos fun i _ => min_le_right _ _
      have h2 : ∑ i ∈ S, min (tExp n (n / 2) ε i) 0 ≤ ∑ i ∈ S, tExp n (n / 2) ε i :=
        Finset.sum_le_sum fun i _ => min_le_left _ _
      linarith
    have := key (Finset.univ.filter fun j => tExp n (n / 2) κ j < 0) _ (fun S _ => hS S)
    rw [Finset.sum_filter] at this
    have h3 : ∑ j, (if tExp n (n / 2) κ j < 0 then tExp n (n / 2) κ j else 0) =
        ∑ j, min (tExp n (n / 2) κ j) 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · exact (min_eq_left h.le).symm
      · exact (min_eq_right (not_lt.mp h)).symm
    rw [h3, sum_min_tExp] at this
    linarith

end GlobalTheory.LFun.CellBound

end
end

section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (ε κ : Fin (n / 2) → ℤ) (u k k₁ k₂ : GU σ n), (∀ i, |ε i| ≤ 1) → IsUnipU u → k ∈ KU σ n → k₁ ∈ KU σ n → k₂ ∈ KU σ n → tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tMat ϖ n (n / 2) ε * ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i| := by
  first | exact @GlobalTheory.LFun.CellBound.cell_bound | exact GlobalTheory.LFun.CellBound.cell_bound | (intros; apply GlobalTheory.LFun.CellBound.cell_bound <;> assumption)
end

section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | exact GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | (intros; apply GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL <;> assumption)
end

section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_elementaryDivisors_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧ ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L), ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  first | exact @GlobalTheory.LFun.UnitaryDiv.exists_good_div | exact GlobalTheory.LFun.UnitaryDiv.exists_good_div | (intros; apply GlobalTheory.LFun.UnitaryDiv.exists_good_div <;> assumption)
end

section
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun

open Polynomial in

theorem exists_multiset_esymm_eq (n : ℕ) (e : ℕ → ℂ) (h0 : e 0 = 1) (hn : e n ≠ 0) :
    ∃ A : Multiset ℂ, A.card = n ∧ (0 : ℂ) ∉ A ∧ ∀ j ≤ n, A.esymm j = e j := by
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), monomial k ((-1) ^ (n - k) * e (n - k)) with hp
  have hc : ∀ k, p.coeff k = if k ≤ n then (-1) ^ (n - k) * e (n - k) else 0 := fun k => by
    simp [hp, coeff_monomial]
  have hle : p.natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [hc, if_neg (by omega)]
  have hcn : p.coeff n = 1 := by simp [hc, h0]
  have hd : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcn])
  have hl : p.leadingCoeff = 1 := by rw [leadingCoeff, hd, hcn]
  have hr : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  refine ⟨p.roots, hr.trans hd, fun hz => ?_, fun j hj => ?_⟩
  · have := isRoot_of_mem_roots hz
    rw [IsRoot, ← coeff_zero_eq_eval_zero, hc] at this
    simp [hn] at this
  · have := coeff_eq_esymm_roots_of_card hr (k := n - j) (by omega)
    rw [hc, if_pos (by omega), hl, hd, one_mul, Nat.sub_sub_self hj] at this
    exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this).symm

theorem exists_satEig_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 →
    ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  intro q n hq c h0 hn
  have hw : ∀ j : ℕ, (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) ≠ 0 := fun j h =>
    hq (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h).1)
  obtain ⟨A, hA, hz, he⟩ := exists_multiset_esymm_eq n
    (fun j => c j / (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) (by simp [h0]) (div_ne_zero hn (hw n))
  refine ⟨A.pmap (fun a (h : a ≠ 0) => Units.mk0 a h) (fun a ha h => hz (h ▸ ha)), by simp [hA], fun j hj => ?_⟩
  rw [satEig, Multiset.map_pmap]
  simp only [Units.val_mk0, Multiset.pmap_eq_map, Multiset.map_id']
  rw [he j hj]
  exact mul_div_cancel₀ _ (hw j)

end GlobalTheory.LFun
end

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiset_satakeEigenvalue_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 → ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  atlas_forward_decl GlobalTheory.LFun.exists_satEig_eq
end

section
noncomputable section

namespace GlobalTheory.LFun.SatCompare

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp NumberField IsDedekindDomain

section Induced

variable {G M V : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T1Space M] [AddCommGroup V] [Module ℂ V] (P : LeviDatum G M) (χ : M →* ℂˣ) {K : Subgroup G}

theorem exists_fun_of_isSubquot (hK : IsCompact (K : Set G)) (hc : IsCommensurated K) {π : Representation ℂ G V}
    (h : IsSubquot π (P.nInd (charRep χ))) {x : V} (hx : x ∈ fixed π K) (h0 : x ≠ 0) :
    ∃ φ : G → ℂ, φ ≠ 0 ∧ (∀ (b : P.Q) g, ∀ k ∈ K, φ (b * g * k) = (P.deltaHalf b : ℂ) * χ (P.p b) * φ g) ∧
      ∀ f ∈ Hecke ℂ K, ∀ c : ℂ, heckeVec (rightReg ℂ G ℂ) K f φ = c • φ → heckeVec π K f x = c • x := by
  obtain ⟨S, p, hp⟩ := h
  have hS : IsSmooth S.toRepresentation := fun v => by
    refine (congrArg IsOpen ?_).mpr (P.nInd_isSmooth (charRep χ) v.1)
    ext g
    exact Subtype.ext_iff
  rw [← GlobalTheory.LocGL.map_fixed_of_surjective hS hK hp] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  let ι : S.toSubmodule →ₗ[ℂ] (G → ℂ) := (Submodule.subtype _).comp ((Submodule.subtype _).comp S.toSubmodule.subtype)
  have hι : Function.Injective ι := fun a b e => Subtype.ext (Subtype.ext (Subtype.ext e))
  refine ⟨ι y, fun e => h0 ?_, fun b g k hk => ?_, fun f hf c e => ?_⟩
  · rw [hι (e.trans (map_zero ι).symm), map_zero]
  · have h1 : ι y (b * g * k) = ι y (b * g) := congrFun (congrArg ι (mem_fixed.1 hy k hk)) (b * g)
    rw [h1]
    exact (LeviDatum.IndSpace.law P y.1 b g).trans (by rw [charRep_apply, smul_eq_mul, ← mul_assoc]; rfl)
  · rw [← map_heckeVec (ρ := S.toRepresentation) hc hf ι (fun _ _ => rfl), ← map_smul] at e
    rw [← map_heckeVec (ρ := S.toRepresentation) hc hf p.toLinearMap (fun g v => p.isIntertwining _ _ g v), hι e,
      map_smul]

theorem exists_fixed_of_fun (hK : IsOpen (K : Set G)) (hc : IsCommensurated K) {φ : G → ℂ} (h0 : φ ≠ 0)
    (hφ : ∀ (b : P.Q) g, ∀ k ∈ K, φ (b * g * k) = (P.deltaHalf b : ℂ) * χ (P.p b) * φ g) :
    ∃ y ∈ fixed (P.nInd (charRep χ)) K, y ≠ 0 ∧ ∀ f ∈ Hecke ℂ K, ∀ c : ℂ,
      heckeVec (rightReg ℂ G ℂ) K f φ = c • φ → heckeVec (P.nInd (charRep χ)) K f y = c • y := by
  have hr : ∀ k ∈ K, ∀ g, φ (g * k) = φ g := fun k hk g => by simpa using hφ 1 g k hk
  let z : indSpace P.Q (LGrp.twist P.deltaHalf ((charRep χ).comp P.p)) := ⟨φ, fun b g => by
    have := hφ b g 1 (one_mem _)
    rw [mul_one] at this
    rw [this, twist_apply, MonoidHom.comp_apply, charRep_apply, smul_eq_mul, mul_assoc]⟩
  have hz : z ∈ smoothPart (ind P.Q (LGrp.twist P.deltaHalf ((charRep χ).comp P.p))) :=
    GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem _)) fun g hg =>
      Subtype.ext (funext (hr g hg)))
  let ι : P.IndSpace (charRep χ) →ₗ[ℂ] (G → ℂ) := (Submodule.subtype _).comp (Submodule.subtype _)
  have hι : Function.Injective ι := fun a b e => Subtype.ext (Subtype.ext e)
  refine ⟨⟨z, hz⟩, mem_fixed.2 fun k hk => hι (funext (hr k hk)), fun e => h0 (congrArg ι e), fun f hf c e => hι ?_⟩
  rw [map_heckeVec (ρ' := rightReg ℂ G ℂ) hc hf ι (fun _ _ => rfl), map_smul]
  exact e

end Induced

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GU σ n) V} {α : Fin (n / 2) → ℂˣ}

end Unitary

section Linear

open GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
  {B : Multiset ℂˣ}

theorem ne_zero_of_isUnifV {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at h

theorem satEig_self_ne_zero (hB : B.card = n) : satEig (qV E w) n B n ≠ 0 := by
  have hp := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
  rw [Multiset.card_map, hB] at hp
  simp [satEig, Multiset.esymm, hp]

theorem exists_eigenvalue_GL {x : V} {y : W} (hx : IsSatVecGL w π x B) (hy : IsSatVecGL w ρ y B) :
    ∀ f ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, heckeVec π (KGL w n) f x = c • x ∧ heckeVec ρ (KGL w n) f y = c • y := by
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  let A : Submodule ℂ (GL (Fin n) (w.adicCompletion E) → ℂ) :=
    { carrier := {f | f ∈ Hecke ℂ (KGL w n) ∧
        ∃ c : ℂ, heckeVec π (KGL w n) f x = c • x ∧ heckeVec ρ (KGL w n) f y = c • y}
      zero_mem' := ⟨zero_mem _, 0, by simp [heckeVec_zero_left]⟩
      add_mem' := by
        rintro f f' ⟨hf, c, e1, e2⟩ ⟨hf', c', e1', e2'⟩
        exact ⟨add_mem hf hf', c + c', by rw [heckeVec_add_left hK hf hf', e1, e1', add_smul],
          by rw [heckeVec_add_left hK hf hf', e2, e2', add_smul]⟩
      smul_mem' := by
        rintro a f ⟨hf, c, e1, e2⟩
        exact ⟨Submodule.smul_mem _ a hf, a * c, by rw [heckeVec_smul_left hK hf, e1, mul_smul],
          by rw [heckeVec_smul_left hK hf, e2, mul_smul]⟩ }
  have hT : ∀ j ≤ n, Tj ℂ n (Ov E w) ϖ j ∈ A := fun j hj =>
    ⟨Tj_mem_hecke hu j, _, hx.2.2.2 ϖ hu j hj, hy.2.2.2 ϖ hu j hj⟩
  have hc : ∀ f ∈ A, ∀ f' ∈ A, conv (KGL w n) f f' ∈ A := by
    rintro f ⟨hf, c, e1, e2⟩ f' ⟨hf', c', e1', e2'⟩
    exact ⟨Final.HeckeConvMem _ _ ℂ hK _ hf _ hf', c' * c,
      by rw [heckeVec_conv hK hf hf' hx.2.1, e1', heckeVec_smul hK hf, e1, mul_smul],
      by rw [heckeVec_conv hK hf hf' hy.2.1, e2', heckeVec_smul hK hf, e2, mul_smul]⟩
  have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1) := by
    rw [Tj_eq h0]; simp
  have shift : ∀ g, dosetInd ℂ (KGL w n) (tor h0 (fun _ => 1) * g) ∈ A → dosetInd ℂ (KGL w n) g ∈ A := by
    intro g hg
    have hz := Final.DosetIndMem _ (KGL w n) ℂ (tor h0 fun _ => 1)
    have hg' := Final.DosetIndMem _ (KGL w n) ℂ g
    have hcv : conv (KGL w n) (dosetInd ℂ (KGL w n) g) (dosetInd ℂ (KGL w n) (tor h0 fun _ => 1)) ∈ A := by
      refine mem_of_supp A (Final.HeckeConvMem _ _ ℂ hK _ hg' _ hz) fun x hx => ?_
      obtain ⟨y, z, ⟨a, ha, b, hb, rfl⟩, ⟨c, hc, d, hd, rfl⟩, rfl⟩ := conv_supp hK hx
      rwa [dosetInd_congr ⟨a, ha, b * c * d, mul_mem (mul_mem hb hc) hd, ?_⟩]
      have := tor_const_comm h0 1 (g * b * c)
      calc a * g * b * (c * tor h0 (fun _ => 1) * d) = a * (g * b * c * tor h0 (fun _ => 1)) * d := by group
        _ = _ := by rw [← this]; group
    obtain ⟨-, c, e1, e2⟩ := hcv
    have hne := satEig_self_ne_zero (w := w) hx.2.2.1
    rw [heckeVec_conv hK hg' hz hx.2.1, ← hTn, hx.2.2.2 ϖ hu n le_rfl, heckeVec_smul hK hg'] at e1
    rw [heckeVec_conv hK hg' hz hy.2.1, ← hTn, hy.2.2.2 ϖ hu n le_rfl, heckeVec_smul hK hg'] at e2
    exact ⟨hg', (satEig (qV E w) n B n)⁻¹ * c, by rw [mul_smul, ← e1, inv_smul_smul₀ hne],
      by rw [mul_smul, ← e2, inv_smul_smul₀ hne]⟩
  have hall : ∀ (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, 0 ≤ a i + N) →
      dosetInd ℂ (KGL w n) (tor h0 a) ∈ A := by
    intro N
    induction N with
    | zero =>
      intro a ha ha0
      obtain ⟨d, rfl⟩ : ∃ d : Fin n → ℕ, a = fun i => (d i : ℤ) :=
        ⟨fun i => (a i).toNat, funext fun i => (Int.toNat_of_nonneg (by simpa using ha0 i)).symm⟩
      exact gen_nat h0 hu A hT hc _ _ d (fun a b hab => Int.ofNat_le.1 (ha hab)) rfl rfl
    | succ N ih =>
      intro a ha ha0
      refine shift _ ?_
      rw [← tor_add]
      refine ih _ (fun i j hij => ?_) fun i => ?_
      · have := ha hij
        simp only [Pi.add_apply]; omega
      · have := ha0 i
        simp only [Pi.add_apply]; omega
  intro h hh
  refine (mem_of_supp A hh fun g _ => ?_).2
  obtain ⟨a, ha, hg⟩ := cartan h0 hu g
  rw [dosetInd_congr hg]
  refine hall (∑ i, (a i).natAbs) a ha fun i => ?_
  have := Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

variable (w n) in
theorem isOpen_isCompact_KGL : IsOpen (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) ∧
    IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  rw [KGL, ← GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  exact ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩

theorem isSphericalGL_iff (α : Fin n → ℂˣ) (φ : GL (Fin n) (w.adicCompletion E) → ℂ) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    Formalism.UG.IsSpherical E w (fun i => (α i : ℂ)) φ ↔
      ∀ (b : (borelGL (w.adicCompletion E) (Fin n)).Q) g, ∀ k ∈ KGL w n, φ (b * g * k) =
        ((borelGL (w.adicCompletion E) (Fin n)).deltaHalf b : ℂ) *
          unrTorus (vZ (w.adicCompletion E)) α ((borelGL (w.adicCompletion E) (Fin n)).p b) * φ g := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have e0 : unrTorus (vZ (w.adicCompletion E)) α = unrTorus
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom α := by
    refine MonoidHom.ext fun t => ?_
    rw [unrTorus_apply, unrTorus_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [unrChar_eq, GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion]
    rfl
  have e := GlobalTheory.LGrp.BorelCompletion.deltaHalf_mul_unrTorus E w n α
  rw [e0]
  constructor
  · intro h b g k hk
    rw [h b g k (fun _ _ hij => b.2 hij) hk, ← e b]
  · intro h b g k hb hk
    rw [h ⟨b, fun _ _ hij => hb _ _ hij⟩ g k hk, ← e ⟨b, fun _ _ hij => hb _ _ hij⟩]

theorem hasSatGL_of_hasSatakeGL :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatakeGL π B → HasSatGL w π B := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  rintro ⟨⟨α, rfl, -, hq⟩, hs⟩
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hs
  refine ⟨hs, fun x hx h0 => ⟨h0, hx, by simp, fun ϖ hϖ j hj => ?_⟩⟩
  obtain ⟨φ, hφ0, hφ, ht⟩ := exists_fun_of_isSubquot _ _ (isOpen_isCompact_KGL w n).2 (Final.GLintComm E w n) hq hx h0
  exact ht _ (Tj_mem_hecke hϖ j) _ ((isSatVecGL_of_isSpherical ((isSphericalGL_iff α φ).2 hφ) hφ0).2.2.2 ϖ hϖ j hj)

theorem hasSatakeGL_of_isSatVecGL (hπ : IsIrrSmooth π) {x : V} (hx : IsSatVecGL w π x B) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatakeGL π B := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = n := hx.2.2.1
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at h1
  obtain ⟨ho, hc⟩ := isOpen_isCompact_KGL w n
  obtain ⟨y, hy, hy0, ht⟩ := exists_fixed_of_fun _ _ ho (Final.GLintComm E w n) hφ0 ((isSphericalGL_iff α φ).1 hφ)
  refine ⟨⟨α, rfl, hπ, GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues _ _ _ π _ _ hc (Final.GLintComm E w n) hπ (LeviDatum.nInd_isSmooth _ _) x hx.2.1
    hx.1 y hy hy0 fun f hf => ?_⟩, ?_⟩
  · obtain ⟨c, e1, e2⟩ := exists_eigenvalue_GL hx (isSatVecGL_of_isSpherical hφ hφ0) f hf
    exact ⟨c, e1, ht f hf c e2⟩
  · rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact (Submodule.ne_bot_iff _).2 ⟨x, hx.2.1, hx.1⟩

theorem hasSatakeGL_iff :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatakeGL π B ↔ IsIrrSmooth π ∧ HasSatGL w π B :=
  ⟨fun h => ⟨h.1.choose_spec.2.1, hasSatGL_of_hasSatakeGL h⟩, fun h => by
    obtain ⟨x, hx⟩ := h.2.exists_vec
    exact hasSatakeGL_of_isSatVecGL h.1 hx⟩

theorem exists_hasSatGL (hπ : IsIrrSmooth π) (hf : FiniteDimensional ℂ (fixed π (KGL w n)))
    (hs : LGrp.IsSpherical π (KGL w n)) : ∃ B, HasSatGL w π B := by
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
  choose c hc using fun j => GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors _ _ π _ (isOpen_isCompact_KGL w n).2 hK (Final.HeckeCommGL E w n ℂ) hπ hf _
    (Tj_mem_hecke hu j)
  have c0 : c 0 = 1 := by
    have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w n) 1 := by
      rw [Tj_eq h0]
      congr 1
    refine smul_left_injective ℂ hx0 ?_
    simp only [← hc 0 x hx, e, heckeVec_one hK hx, one_smul]
  have cn : c n ≠ 0 := by
    intro e
    have h1 := hc n x hx
    have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1) := by
      rw [Tj_eq h0]; simp
    rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
    · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
    · intro γ hγ
      exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
    · intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
      refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
      rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
      exact mul_mem ha hb
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) n (qV_ne_zero w) c c0 cn
  refine ⟨B, hs, fun y hy hy0 => ⟨hy0, hy, hB, fun ϖ' hu' j hj => ?_⟩⟩
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rw [div_mul_cancel₀ _ h0] at e
  rw [e, hc j y hy, hBc j hj]

end Linear

section Characters

theorem exists_algHom_extend {A : Type} [CommRing A] [Algebra ℂ A] (B : Subalgebra ℂ A) [Module.Finite B A]
    (χ : B →ₐ[ℂ] ℂ) : ∃ ψ : A →ₐ[ℂ] ℂ, ∀ b : B, ψ b = χ b := by
  have hs : Function.Surjective χ := fun c => ⟨algebraMap ℂ B c, by simp⟩
  haveI := RingHom.ker_isMaximal_of_surjective χ.toRingHom hs
  obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (RingHom.ker χ.toRingHom) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
  have key : ∀ b : B, Ideal.Quotient.mk Q b = algebraMap ℂ (A ⧸ Q) (χ b) := fun b => by
    have : b - algebraMap ℂ B (χ b) ∈ Q.comap (algebraMap B A) := by
      rw [e, RingHom.mem_ker]; simp
    exact Ideal.Quotient.eq.2 this
  letI := Ideal.Quotient.field Q
  haveI : Algebra.IsIntegral ℂ (A ⧸ Q) := ⟨fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact (Algebra.IsIntegral.isIntegral (R := B) a).map_of_comp_eq χ.toRingHom (Ideal.Quotient.mk Q)
      (RingHom.ext fun b => (key b).symm)⟩
  let i := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ Q)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨i.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q), fun b => ?_⟩
  exact i.symm_apply_eq.2 (key b)

variable {m : ℕ}

def ev (α : Fin m → ℂˣ) : AddMonoidAlgebra ℂ (Fin m → ℤ) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin m → ℤ)
    { toFun := fun a => ∏ i, (α i : ℂ) ^ a.toAdd i
      map_one' := by simp
      map_mul' := fun a b => by simp [zpow_add₀, Finset.prod_mul_distrib] }

theorem ev_apply (α : Fin m → ℂˣ) (s : AddMonoidAlgebra ℂ (Fin m → ℤ)) :
    ev α s = s.coeff.sum fun a c => c * ∏ i, (α i : ℂ) ^ a i := by
  rw [ev, AddMonoidAlgebra.lift_apply]
  rfl

theorem exists_eq_ev (ψ : AddMonoidAlgebra ℂ (Fin m → ℤ) →ₐ[ℂ] ℂ) : ∃ α, ψ = ev α := by
  obtain ⟨F, rfl⟩ := (AddMonoidAlgebra.lift ℂ ℂ (Fin m → ℤ)).surjective ψ
  refine ⟨fun i => F.toHomUnits (Multiplicative.ofAdd (Pi.single i 1)), congrArg _ (MonoidHom.ext fun a => ?_)⟩
  have : a = ∏ i, Multiplicative.ofAdd (Pi.single i 1 : Fin m → ℤ) ^ a.toAdd i := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    conv_lhs => rw [← Finset.univ_sum_single a.toAdd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toAdd_zpow, toAdd_ofAdd, ← Pi.single_smul, smul_eq_mul, mul_one]
  show F a = ∏ i, ((F.toHomUnits (Multiplicative.ofAdd (Pi.single i 1)) : ℂˣ) : ℂ) ^ a.toAdd i
  conv_lhs => rw [this, ← F.coe_toHomUnits, map_prod, Units.coe_prod]
  simp only [map_zpow, Units.val_zpow_eq_zpow_val]

end Characters

section Existence

open GlobalTheory.InertThetaCompare GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem satU_laws (hU : IsUnramInv ϖ σ q) (α : Fin (n / 2) → ℂˣ) :
    (∀ f ∈ Hecke ℂ (KU σ n), ∀ f' ∈ Hecke ℂ (KU σ n), SatU ϖ q (f + f') (fun i => (α i : ℂ)) =
      SatU ϖ q f (fun i => (α i : ℂ)) + SatU ϖ q f' (fun i => (α i : ℂ))) ∧
    (∀ (c : ℂ), ∀ f ∈ Hecke ℂ (KU σ n), SatU ϖ q (c • f) (fun i => (α i : ℂ)) = c * SatU ϖ q f (fun i => (α i : ℂ))) ∧
    SatU ϖ q (dosetInd ℂ (KU σ n) 1) (fun i => (α i : ℂ)) = 1 := by
  obtain ⟨x, h0, hx, e⟩ := (hasSatU_psFunU hU α).exists_vec
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  refine ⟨fun f hf f' hf' => smul_left_injective ℂ h0 ?_, fun c f hf => smul_left_injective ℂ h0 ?_,
    smul_left_injective ℂ h0 ?_⟩
  · simp only [← e _ (add_mem hf hf'), heckeVec_add_left hK hf hf', e _ hf, e _ hf', add_smul]
  · simp only [← e _ (Submodule.smul_mem _ c hf), heckeVec_smul_left hK hf, e _ hf, mul_smul]
  · simp only [← e _ (Final.DosetIndMem _ _ ℂ 1), heckeVec_one hK hx, one_smul]

omit [CompleteSpace L] in
theorem labInd_eq {d : List ℤ} {t : GU σ n}
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i : Fin n => ϖ ^ d.getD i.1 0) :
    labInd σ n ϖ d = dosetInd ℂ (KU σ n) t := by
  unfold labInd dosetInd
  congr 1
  ext g
  rw [GlobalTheory.WeylGL.mem_doset, ← ht]
  simp only [Set.mem_setOf_eq, ← Units.val_mul, Units.val_inj, ← Subgroup.coe_mul, Subtype.val_inj]

theorem exists_labInd_eq (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ d, Good n d ∧ labInd σ n ϖ d = dosetInd ℂ (KU σ n) g := by
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.T.exists_symmetric_elementaryDivisors_unitary L ϖ σ q n hU g
  obtain ⟨t, ht⟩ := exists_diag hU hd
  refine ⟨d, hd, (labInd_eq ht).trans (GlobalTheory.WeylGL.dosetInd_congr ?_).symm⟩
  exact GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset L ϖ σ q n hU t g a b ha hb (Units.ext (by rw [e, ← ht]; rfl))

theorem eq_zero_of_satU (hU : IsUnramInv ϖ σ q) {f : GU σ n → ℂ} (hf : f ∈ Hecke ℂ (KU σ n))
    (h : ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q f (fun i => (α i : ℂ)) = 0) : f = 0 := by
  have hm : ∀ d, Good n d → labInd σ n ϖ d ∈ Hecke ℂ (KU σ n) := fun d hd => by
    obtain ⟨t, ht⟩ := exists_diag hU hd
    rw [labInd_eq ht]
    exact Final.DosetIndMem _ _ ℂ t
  have h1 : f ∈ Submodule.span ℂ (labInd σ n ϖ '' {d | Good n d}) :=
    GlobalTheory.WeylGL.mem_of_supp _ hf fun g _ => Submodule.subset_span (exists_labInd_eq hU g)
  obtain ⟨s, hs, c, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun ℂ).1 h1
  classical
  let c' : List ℤ → ℂ := fun d => if h : d ∈ s then c ⟨d, h⟩ else 0
  have e : ∑ i : s, c i • labInd σ n ϖ i = ∑ d ∈ s, c' d • labInd σ n ϖ d := by
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ => by simp [c']
  rw [e] at h ⊢
  have h2 : ∀ (α : Fin (n / 2) → ℂˣ) (s' : Finset (List ℤ)), (∀ d ∈ s', Good n d) →
      SatU ϖ q (∑ d ∈ s', c' d • labInd σ n ϖ d) (fun i => (α i : ℂ)) =
        ∑ d ∈ s', c' d * SatU ϖ q (labInd σ n ϖ d) (fun i => (α i : ℂ)) := fun α s' => by
    obtain ⟨ha, hb, -⟩ := satU_laws (n := n) hU α
    induction s' using Finset.induction_on with
    | empty => intro _; simpa using hb 0 0 (zero_mem _)
    | insert d s' hd ih =>
      intro hg
      have g1 := hm d (hg d (Finset.mem_insert_self _ _))
      have g2 := fun d hd => hg d (Finset.mem_insert_of_mem hd)
      rw [Finset.sum_insert hd, Finset.sum_insert hd, ha _ (Submodule.smul_mem _ _ g1) _
        (Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (hm d (g2 d hd))), hb _ _ g1, ih g2]
  have h3 := GlobalTheory.InertThetaCompare.satU_indep hU s c' (fun d hd => hs hd) fun α hα =>
    (h2 (fun i => Units.mk0 _ (hα i)) s fun d hd => hs hd).symm.trans (h _)
  exact Finset.sum_eq_zero fun d hd => by rw [h3 d hd, zero_smul]

theorem exists_satU_eq (hU : IsUnramInv ϖ σ q) (l : Hecke ℂ (KU σ n) →ₗ[ℂ] ℂ)
    (h1 : l ⟨_, Final.DosetIndMem _ _ ℂ 1⟩ = 1)
    (hm : ∀ f f' : Hecke ℂ (KU σ n),
      l ⟨_, Final.HeckeConvMem _ _ ℂ (P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f') :
    ∃ α : Fin (n / 2) → ℂˣ, ∀ f : Hecke ℂ (KU σ n), l f = SatU ϖ q f.1 fun i => (α i : ℂ) := by
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have law := satU_laws (n := n) hU
  have hmul := fun (α : Fin (n / 2) → ℂˣ) => Final.SatMul L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  let R : AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ) → Hecke ℂ (KU σ n) → Prop := fun b f =>
    ∀ α : Fin (n / 2) → ℂˣ, ev α b = SatU ϖ q f.1 fun i => (α i : ℂ)
  have Radd : ∀ {a b f g}, R a f → R b g → R (a + b) (f + g) := fun {a b f g} e e' α => by
    rw [map_add, e, e']; exact ((law α).1 _ f.2 _ g.2).symm
  have Rmul : ∀ {a b f g}, R a f → R b g → R (a * b) ⟨_, Final.HeckeConvMem _ _ ℂ hK _ f.2 _ g.2⟩ :=
    fun {a b f g} e e' α => by rw [map_mul, e, e']; exact (hmul α _ f.2 _ g.2).symm
  have Ralg : ∀ c : ℂ, R (algebraMap ℂ _ c) (c • ⟨_, Final.DosetIndMem _ _ ℂ 1⟩) := fun c α => by
    rw [AlgHom.commutes]
    exact (((law α).2.1 c _ (Final.DosetIndMem _ _ ℂ 1)).trans (by rw [(law α).2.2, mul_one]; rfl)).symm
  have Runiq : ∀ {a f g}, R a f → R a g → f = g := fun {a f g} e e' => by
    refine sub_eq_zero.1 (Subtype.ext (eq_zero_of_satU hU (f - g).2 fun α => ?_))
    have := (law α).1 _ (f - g).2 _ g.2
    rw [← Submodule.coe_add, sub_add_cancel, ← e, ← e'] at this
    exact right_eq_add.1 this
  let B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ)) :=
    { carrier := {b | ∃ f, R b f}
      mul_mem' := fun ⟨_, e⟩ ⟨_, e'⟩ => ⟨_, Rmul e e'⟩
      add_mem' := fun ⟨_, e⟩ ⟨_, e'⟩ => ⟨_, Radd e e'⟩
      algebraMap_mem' := fun c => ⟨_, Ralg c⟩ }
  choose φ hφ using fun b : B => b.2
  let χ : B →ₐ[ℂ] ℂ :=
    { toFun := fun b => l (φ b)
      map_one' := by rw [Runiq (hφ 1) (Ralg 1), one_smul, h1]
      map_mul' := fun a b => by rw [Runiq (hφ (a * b)) (Rmul (hφ a) (hφ b)), hm]
      map_zero' := by rw [Runiq (hφ 0) (by simpa using Ralg 0 : R 0 0), map_zero]
      map_add' := fun a b => by rw [Runiq (hφ (a + b)) (Radd (hφ a) (hφ b)), map_add]
      commutes' := fun c => by rw [Runiq (hφ (algebraMap ℂ B c)) (Ralg c), map_smul, h1]; simp }
  have hR : ∀ (f : Hecke ℂ (KU σ n)) (s : (Fin (n / 2) → ℤ) →₀ ℂ),
      (∀ α : Fin (n / 2) → ℂ, SatU ϖ q f.1 α = s.sum fun a c => c * ∏ i, α i ^ a i) → R (.ofCoeff s) f :=
    fun f s e α => by rw [ev_apply, e]
  haveI : Module.Finite B (AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ)) := by
    refine GlobalTheory.T.laurent_finite_of_triangular_signed_indicators _ B fun ε hε => ?_
    obtain ⟨t, ht⟩ := P.fSatake_tMat_exists (n := n) hU (Nat.mul_div_le n 2) ε
    obtain ⟨s, e, hs, ht'⟩ := GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial L ϖ σ q n hU _ (Final.DosetIndMem _ (KU σ n) ℂ t)
    refine ⟨.ofCoeff s, ⟨_, hR ⟨_, Final.DosetIndMem _ (KU σ n) ℂ t⟩ s e⟩, ht' t ε ht rfl, fun κ hκ => ?_⟩
    obtain ⟨g, hg, u, hu, k, hk, eg⟩ := hs κ hκ
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g = a * t * b := by
      by_contra h0
      exact hg (GlobalTheory.WeylGL.dosetInd_of_not h0)
    exact GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset L ϖ σ q n hU ε κ u k a b hε hu hk ha hb (by rw [← eg, ← ht]; rfl)
  obtain ⟨ψ, hψ⟩ := exists_algHom_extend B χ
  obtain ⟨α, rfl⟩ := exists_eq_ev ψ
  refine ⟨α, fun f => ?_⟩
  obtain ⟨s, e, -⟩ := GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial L ϖ σ q n hU _ f.2
  have r := hR f s e
  rw [← r α, hψ ⟨_, f, r⟩]
  exact congrArg l (Runiq r (hφ ⟨_, f, r⟩))

variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GU σ n) V}

theorem exists_hasSatU (hU : IsUnramInv ϖ σ q) (hπ : IsIrrSmooth π) (hf : FiniteDimensional ℂ (fixed π (KU σ n)))
    (hs : LGrp.IsSpherical π (KU σ n)) : ∃ α, HasSatU ϖ q π α := by
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hs
  choose c hc using fun f : Hecke ℂ (KU σ n) => GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors _ _ π _ (GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints L ϖ σ q n hU).2 hK
    (GlobalTheory.UnitarySwap.heckeCommU L ϖ σ q n ℂ hU) hπ hf _ f.2
  let l : Hecke ℂ (KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun f g => smul_left_injective ℂ h0 (by
        simp only [add_smul, ← hc _ x hx]; exact heckeVec_add_left hK f.2 g.2 x)
      map_smul' := fun a f => smul_left_injective ℂ h0 (by
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul, ← hc _ x hx]; exact heckeVec_smul_left hK f.2 a x) }
  obtain ⟨α, hα⟩ := exists_satU_eq hU l
    (smul_left_injective ℂ h0 ((hc _ x hx).symm.trans ((heckeVec_one hK hx).trans (one_smul _ _).symm)))
    fun f g => smul_left_injective ℂ h0 ((hc _ x hx).symm.trans ((heckeVec_conv hK f.2 g.2 hx).trans (by
      rw [hc g x hx, heckeVec_smul hK f.2, hc f x hx, smul_smul, mul_comm]; rfl)))
  exact ⟨α, hs, fun y hy hy0 => ⟨hy0, hy, fun f hf => (hc ⟨f, hf⟩ y hy).trans (by rw [← hα ⟨f, hf⟩]; rfl)⟩⟩

end Existence

end GlobalTheory.LFun.SatCompare

end
end
