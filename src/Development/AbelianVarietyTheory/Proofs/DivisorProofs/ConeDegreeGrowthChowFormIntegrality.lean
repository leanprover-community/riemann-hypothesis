import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSection
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConductorNeZeroFiniteTypeCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLinearSystemConeAlgebraIffCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexPointNormLtOfNotIsUnit

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

namespace GlobalTheory.DegCmp

theorem rank_map_eq_of_ker_iff {K M A B : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (S : Submodule K M) (f : M →ₗ[K] A) (g : M →ₗ[K] B)
    (h : ∀ x ∈ S, f x = 0 ↔ g x = 0) :
    Module.rank K (S.map f) = Module.rank K (S.map g) := by
  have hk : LinearMap.ker (f.domRestrict S) = LinearMap.ker (g.domRestrict S) := by
    ext x
    simpa using h x x.2
  rw [← LinearMap.range_domRestrict, ← LinearMap.range_domRestrict,
    ← (LinearMap.quotKerEquivRange _).rank_eq, ← (LinearMap.quotKerEquivRange _).rank_eq, hk]

theorem range_pow_eq_map_homogeneous {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) (τ : ℕ) :
    ((LinearMap.range ev) ^ τ : Submodule K Ω) =
      (homogeneousSubmodule (Fin N) K τ).map (aeval (fun j => ev (b j)) : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← homogeneousSubmodule_one_pow, Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span,
    LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 3
  ext j
  simp

theorem hilb_eq_finrank_quotPiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  intro K V Ω _ _ _ _ _ ev N b τ
  rw [hilb, range_pow_eq_map_homogeneous ev b τ, GlobalTheory.quotPiece_natCast,
    rank_map_eq_of_ker_iff _ _ (Ideal.Quotient.mkₐ K (imageIdeal ev b)).toLinearMap, ← Module.finrank_eq_rank]
  · simp
  · intro x hx
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_coneIdeal_of_isHomogeneous _ hx).symm

end GlobalTheory.DegCmp
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSystemHilbertFunction_eq_finrank_conePiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | exact GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | (intros; apply GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowthLimsup_of_eventually_polynomial : ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) → (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D → growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧ ((D : WithBot ℕ) < H.degree → growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  first | exact @GlobalTheory.CompHt.growth_of_eventually_eq_eval | exact GlobalTheory.CompHt.growth_of_eventually_eq_eval | (intros; apply GlobalTheory.CompHt.growth_of_eventually_eq_eval <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chowForm_of_homogeneous_prime_krullDim : ∀ (K : Type) [Field K] (N D : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) → ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  first | exact @GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | exact GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | (intros; apply GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_coneIdeal_eq_field_degree : ∀ (K : Type) [Field K] (N : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 → GlobalTheory.idealHilbertPoly (coneIdeal K y) = Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  first | exact @GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | exact GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | (intros; apply GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_degree_le_chowForm_degree_algebraic_point : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  first | exact @GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | exact GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chowForm_degree_le_field_degree_algebraic_point : ∀ (K : Type) [Field K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → δ ≤ Module.finrank K (IntermediateField.adjoin K (Set.range y)) := by
  first | exact @GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | exact GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_map_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = GlobalTheory.idealHilbertPoly P := by
  first | exact @GlobalTheory.HilbBaseChange.idealHilbertPoly_map | exact GlobalTheory.HilbBaseChange.idealHilbertPoly_map | (intros; apply GlobalTheory.HilbBaseChange.idealHilbertPoly_map <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrime_map_rationalFunctions_generic_linearForm_not_mem : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧ ((∃ j, X j ∉ P) → (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L) ∉ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  first | exact @GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | exact GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | (intros; apply GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_saturation_generic_hyperplane_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K, y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) → ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} ≤ Q ∧ ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} := by
  first | exact @GlobalTheory.Chow.exists_prime_saturation_generic_section | exact GlobalTheory.Chow.exists_prime_saturation_generic_section | (intros; apply GlobalTheory.Chow.exists_prime_saturation_generic_section <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_and_hilbertPoly_eq_of_prime_in_saturation : ∀ (K : Type) [Field K] (N : ℕ) (I Q : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → Q.IsPrime → I ≤ Q → (∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) → (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧ GlobalTheory.idealHilbertPoly Q = GlobalTheory.idealHilbertPoly I := by
  first | exact @GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | exact GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | (intros; apply GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq <;> assumption)
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chowForm_generic_hyperplane_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)) (D δ : ℕ) (f : MvPolynomial (Fin (D + 1 + 1) × Fin N) K), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → IsChowFormInt P (D + 1) δ f → ∃ f' : MvPolynomial (Fin (D + 1) × Fin N) L, IsChowFormInt (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)}) D δ f' := by
  first | exact @GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section | exact GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section | (intros; apply GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section <;> assumption)
end

section
set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal Topology

namespace GlobalTheory.GrowthShift

theorem eventually_mul_inv_pow_le (D e : ℕ) {a : ℝ≥0∞} (ha : a < 1) :
    ∀ᶠ k : ℕ in atTop, a * ((k : ℝ≥0∞) ^ D)⁻¹ ≤ (((k + e : ℕ) : ℝ≥0∞) ^ D)⁻¹ := by
  lift a to NNReal using ha.ne_top
  have ha' : (a : ℝ) < 1 := by exact_mod_cast ha
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) / (k + (e : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (e : ℝ)).pow D
  filter_upwards [h1.eventually (lt_mem_nhds ha'), eventually_gt_atTop 0] with k hk hk0
  have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk0
  have hke : (0 : ℝ) < ((k : ℝ) + e) ^ D := by positivity
  rw [div_pow, lt_div_iff₀ hke] at hk
  have h2 : (a : ℝ≥0∞) * ((k + e : ℕ) : ℝ≥0∞) ^ D ≤ (k : ℝ≥0∞) ^ D := by
    have h3 : a * ((k + e : ℕ) : NNReal) ^ D ≤ (k : NNReal) ^ D := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hk.le
    exact_mod_cast h3
  have n0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hk0.ne')
  have nt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm, ← div_eq_mul_inv, ENNReal.div_le_iff n0 nt, one_mul]
  exact h2

theorem growth_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  intro D e r
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rw [growth, growth, ← ENNReal.limsup_const_mul_of_ne_top ha.ne_top,
    ← Filter.limsup_nat_add (fun τ : ℕ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D) e]
  refine limsup_le_limsup ((eventually_mul_inv_pow_le D e ha).mono fun k hk => ?_)
  simp only [div_eq_mul_inv]
  rw [mul_left_comm]
  exact mul_le_mul_right hk _

end GlobalTheory.GrowthShift
end

section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowthLimsup_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  first | exact @GlobalTheory.GrowthShift.growth_shift_le | exact GlobalTheory.GrowthShift.growth_shift_le | (intros; apply GlobalTheory.GrowthShift.growth_shift_le <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_forall_complexPoint_extend' : ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by
  first | exact @GlobalTheory.exists_ne_zero_forall_complexPoint_extend | exact GlobalTheory.exists_ne_zero_forall_complexPoint_extend | (intros; apply GlobalTheory.exists_ne_zero_forall_complexPoint_extend <;> assumption)
end

section
set_option autoImplicit false

namespace GlobalTheory.ConeDeg

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

attribute [local instance] MvPolynomial.gradedAlgebra

section Chow

variable {K : Type} [Field K] {N : ℕ}

theorem isHomogeneous_of_component {I : Ideal (MvPolynomial (Fin N) K)}
    (h : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    I.IsHomogeneous (homogeneousSubmodule (Fin N) K) := fun d g hg => by
  have e : ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g d : _) : MvPolynomial (Fin N) K) =
      homogeneousComponent d g := MvPolynomial.decomposition.decompose'_apply g d
  rw [e]
  exact h g hg d

theorem aeval_eq_zero_of_block {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f)
    (t : Fin (D + 1) × Fin N → AlgebraicClosure K) (i : Fin (D + 1)) (ht : ∀ j, t (i, j) = 0) :
    aeval t f = 0 := by
  have h1 := (isMultiHomogeneous_iff_block.1 h.homog).aeval_smul
    (fun l => if l = i then (0 : AlgebraicClosure K) else 1) t
  have h2 : (fun v : Fin (D + 1) × Fin N => (if v.1 = i then (0 : AlgebraicClosure K) else 1) * t v) = t := by
    funext v
    split_ifs with hv
    · obtain ⟨l, j⟩ := v
      obtain rfl : l = i := hv
      rw [ht, mul_zero]
    · rw [one_mul]
  rw [h2, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h.pos.ne']), zero_mul] at h1
  exact h1

theorem not_lt_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} {D D' δ δ' : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} {f' : MvPolynomial (Fin (D' + 1) × Fin N) K}
    (h : IsChowFormInt P D δ f) (h' : IsChowFormInt P D' δ' f') : ¬ D < D' := fun hlt => by
  refine h.ne_zero (map_injective _ (algebraMap K (AlgebraicClosure K)).injective ?_)
  refine MvPolynomial.funext fun u => ?_
  rw [map_zero, map_zero, eval_map, ← aeval_def]
  obtain ⟨y, hy, hP, hu⟩ := (h'.zero_iff _).1 (aeval_eq_zero_of_block h'
    (fun v => if hv : (v.1 : ℕ) < D + 1 then u (⟨v.1, hv⟩, v.2) else 0) (Fin.last _)
    (fun j => dif_neg (by simp; omega)))
  refine (h.zero_iff u).2 ⟨y, hy, hP, fun i => ?_⟩
  have := hu ⟨i, by omega⟩
  simpa only [dif_pos i.2] using this

theorem exists_X_notMem {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) : ∃ j, X j ∉ P := by
  obtain ⟨y, hy, hyI⟩ := h.exists_point
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  exact ⟨j, fun hX => hj (by simpa using hyI _ hX)⟩

theorem ringKrullDim_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) := by
  obtain ⟨j, hj⟩ := exists_X_notMem h
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ (isHomogeneous_of_component hP) hj
  obtain ⟨δ', f', h'⟩ := GlobalTheory.T.exists_chowForm_of_homogeneous_prime_krullDim K N e P hp hP he
  obtain rfl : e = D := le_antisymm (not_lt.1 (not_lt_of_isChowFormInt h h'))
    (not_lt.1 (not_lt_of_isChowFormInt h' h))
  exact he

theorem exists_eq_coneIdeal {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {δ : ℕ}
    {f : MvPolynomial (Fin (0 + 1) × Fin N) K} (h : IsChowFormInt P 0 δ f) :
    ∃ (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 ∧ P = coneIdeal K y := by
  obtain ⟨y, hy, hyI⟩ := h.exists_point
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have hj' : y j ≠ 0 := hj
  refine ⟨(y j)⁻¹ • y, j, by simp [hj'], ?_⟩
  rw [coneIdeal_smul (inv_ne_zero hj')]
  have hle : P ≤ coneIdeal K y := fun g hg => (mem_coneIdeal_iff y g).2 fun d => hyI _ (hP g hg d)
  by_contra hne
  have := isPrime_coneIdeal (K := K) y
  have hX : (X j : MvPolynomial (Fin N) K) ∉ coneIdeal K y := fun hX =>
    hj' (by simpa using aeval_eq_zero_of_mem_coneIdeal hX)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ (isHomogeneous_coneIdeal y) hX
  have := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle hne)
  rw [he, ringKrullDim_of_isChowFormInt hP h] at this
  have h2 : (e + 1 + 1 : ℕ) ≤ (0 + 1 : ℕ) := by exact_mod_cast this
  omega

theorem coeff_sub_comp {H : Polynomial ℚ} {D : ℕ} (h : H.natDegree ≤ D + 1) :
    (H - H.comp (Polynomial.X - Polynomial.C ((1 : ℕ) : ℚ))).coeff D = (D + 1) * H.coeff (D + 1) := by
  have e : H.comp (Polynomial.X - Polynomial.C ((1 : ℕ) : ℚ)) = Polynomial.taylor (-1) H := by
    rw [Polynomial.taylor_apply]; simp [sub_eq_add_neg]
  have h1 : (Polynomial.hasseDeriv D H).natDegree ≤ 1 :=
    (Polynomial.natDegree_hasseDeriv_le _ _).trans (by omega)
  rw [e, Polynomial.coeff_sub, Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
  simp [Polynomial.hasseDeriv_coeff, add_comm 1 D]

theorem degree_eq_coeff (D : ℕ) : ∀ (K : Type) [Field K] [CharZero K] (P : Ideal (MvPolynomial (Fin N) K))
    [P.IsPrime], (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ∀ (δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f →
    (δ : ℚ) = (D.factorial : ℚ) * (idealHilbertPoly P).coeff D := by
  induction D with
  | zero =>
    intro K _ _ P _ hP δ f h
    obtain ⟨y, j, hy, rfl⟩ := exists_eq_coneIdeal hP h
    rw [GlobalTheory.T.idealQuotientHilbertPoly_coneIdeal_eq_field_degree K N y j hy, le_antisymm (GlobalTheory.T.chowForm_degree_le_field_degree_algebraic_point K N δ y j f hy h) (GlobalTheory.T.field_degree_le_chowForm_degree_algebraic_point K N δ y j f hy h)]
    simp
  | succ D ih =>
    intro K _ _ P hp hP δ f h
    let L := FractionRing (MvPolynomial (Fin N) K)
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    obtain ⟨hE, hEH⟩ := GlobalTheory.T.idealQuotientHilbertPoly_map_baseChange K L N P hP
    obtain ⟨hEp, hl⟩ := GlobalTheory.T.isPrime_map_rationalFunctions_generic_linearForm_not_mem K L N P hp
    obtain ⟨Q, hQ, hIQ, hsat⟩ := GlobalTheory.T.exists_prime_saturation_generic_hyperplane_section K L N P hp fun u => by
      obtain ⟨y, hy, h1, h2⟩ := (h.zero_iff _).1 (aeval_eq_zero_of_block h
        (fun v => if v.1 = 0 then u v.2 else 0) (Fin.last _) (fun j => if_neg (by simp)))
      exact ⟨y, hy, h1, by simpa using h2 0⟩
    obtain ⟨f', hf'⟩ := GlobalTheory.T.exists_chowForm_generic_hyperplane_section K L N P D δ f hP h
    have hlin : (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
        MvPolynomial (Fin N) L).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X L j).C_mul _
    have hI := isHomogeneous_sup_span_singleton (isHomogeneous_of_component hE) hlin
    obtain ⟨hQh, hQH⟩ := GlobalTheory.T.isHomogeneous_and_hilbertPoly_eq_of_prime_in_saturation L N _ Q (fun g hg n => homogeneousComponent_mem_of_mem hI hg n) hQ hIQ hsat
    have hf'' : IsChowFormInt Q D δ f' := ⟨hf'.homog, hf'.irred, fun u => (hf'.zero_iff u).trans
      (exists_congr fun y => and_congr_right fun hy => and_congr_left fun _ =>
        ⟨fun h1 g hg => by
          obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
          obtain ⟨m, hm⟩ := hsat g hg j
          have := h1 _ hm
          rw [map_mul, map_pow, aeval_X] at this
          exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hj), fun h1 g hg => h1 g (hIQ hg)⟩)⟩
    have hdeg := degree_idealHilbertPoly_eq_of_isPrime (isHomogeneous_of_component hP)
      (ringKrullDim_of_isChowFormInt hP h)
    rw [ih L Q hQh δ f' hf'', hQH,
      idealHilbertPoly_sup_of_isPrime (isHomogeneous_of_component hE) hlin (hl (exists_X_notMem h)), hEH,
      coeff_sub_comp (Polynomial.natDegree_le_of_degree_le hdeg.le), Nat.factorial_succ]
    push_cast
    ring

end Chow

section Growth

variable {K V Ω : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

theorem growth_hilb_eq (ev : V →ₗ[K] Ω) (D a : ℕ) (ha : 1 ≤ a) (δ : ℕ) (h : IsImageDeg ev D δ) :
    growth D (fun k => hilb ev (a * k)) = (a : ℝ≥0∞) ^ D * δ := by
  obtain ⟨N, b, f, hf⟩ := h
  have : (imageIdeal ev b).IsPrime := isPrime_coneIdeal _
  have hI : (imageIdeal ev b).IsHomogeneous (homogeneousSubmodule (Fin N) K) := isHomogeneous_coneIdeal _
  have hP := fun g hg n => homogeneousComponent_mem_of_mem hI (p := g) hg n
  simp only [GlobalTheory.T.linearSystemHilbertFunction_eq_finrank_conePiece K V Ω ev N b]
  exact (GlobalTheory.T.rankGrowthLimsup_of_eventually_polynomial D a _ _ ha (eventually_finrank_quotPiece hI)).1
    (degree_idealHilbertPoly_eq_of_isPrime hI (ringKrullDim_of_isChowFormInt hP hf)).le δ
    (degree_eq_coeff D K _ hP δ f hf)

theorem exists_isImageDeg [FiniteDimensional K V] (ev : V →ₗ[K] Ω) (D a : ℕ) (ha : 1 ≤ a)
    (h0 : growth D (fun k => hilb ev (a * k)) ≠ 0) (h1 : growth D (fun k => hilb ev (a * k)) ≠ ⊤) :
    ∃ δ : ℕ, IsImageDeg ev D δ := by
  let b := Module.finBasis K V
  have hp : (imageIdeal ev b).IsPrime := isPrime_coneIdeal _
  have hI : (imageIdeal ev b).IsHomogeneous (homogeneousSubmodule _ K) := isHomogeneous_coneIdeal _
  have hP := fun g hg n => homogeneousComponent_mem_of_mem hI (p := g) hg n
  simp only [GlobalTheory.T.linearSystemHilbertFunction_eq_finrank_conePiece K V Ω ev _ b] at h0 h1
  obtain ⟨g1, g2⟩ := GlobalTheory.T.rankGrowthLimsup_of_eventually_polynomial D a _ _ ha (eventually_finrank_quotPiece hI)
  have hle := not_lt.1 fun h => h1 (g2 h)
  have hc : (idealHilbertPoly (imageIdeal ev b)).coeff D ≠ 0 := fun h =>
    h0 (by simpa using g1 hle 0 (by simp [h]))
  have hd := Polynomial.natDegree_eq_of_degree_eq_some (le_antisymm hle (Polynomial.le_degree_of_ne_zero hc))
  have hX : ∃ j, X j ∉ imageIdeal ev b := by
    by_contra hX
    push Not at hX
    exact hc (by rw [idealHilbertPoly_eq_zero_of_forall_X_mem hI hX, Polynomial.coeff_zero])
  have hdim := ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hI hX
  rw [hd] at hdim
  obtain ⟨δ, f, hf⟩ := GlobalTheory.T.exists_chowForm_of_homogeneous_prime_krullDim K _ D _ hp hP hdim
  exact ⟨δ, _, b, f, hf⟩

end Growth

section Quot

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

theorem X_pow_mul_C_mem (ev : V →ₗ[K] Ω) {d : ℕ} {t : Ω} (ht : t ∈ ((LinearMap.range ev) ^ d : Submodule K Ω)) :
    (Polynomial.X ^ d * Polynomial.C t : Polynomial Ω) ∈ coneAlg ev := by
  refine (GlobalTheory.T.mem_linearSystemConeAlgebra_iff_coeff K V Ω ev _).2 fun n => ?_
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [one_mul, h]; exact ht
  · rw [zero_mul]; exact zero_mem _

theorem finiteType_coneAlg [FiniteDimensional K V] (ev : V →ₗ[K] Ω) : Algebra.FiniteType K (coneAlg ev) := by
  let b := Module.finBasis K V
  let ψ : V →ₗ[K] Polynomial Ω := (LinearMap.mulLeft K (Polynomial.X : Polynomial Ω)) ∘ₗ
    (IsScalarTower.toAlgHom K Ω (Polynomial Ω)).toLinearMap ∘ₗ ev
  have e : coneAlg ev = Algebra.adjoin K (ψ '' Set.range b) := by
    rw [← Algebra.adjoin_span, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    rfl
  rw [e]
  exact (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, (Set.finite_range b).image ψ, rfl⟩)

theorem growth_rank_le [CharZero K] [FiniteDimensional K V] (ev : V →ₗ[K] Ω) (D a : ℕ) (ha : 1 ≤ a)
    (S : ℕ → Submodule K Ω) (hS : ∀ k, ∀ t ∈ S k, IsIntDeg ev (a * k) t ∧ IsRatio ev (a * k) t) :
    growth D (fun k => Cardinal.toENat (Module.rank K (S k))) ≤ growth D (fun k => hilb ev (a * k)) := by
  have := finiteType_coneAlg ev
  obtain ⟨c, hc, H⟩ := GlobalTheory.T.exists_conductor_ne_zero_finiteType_charZero K (coneAlg ev) (Polynomial Ω) Subtype.val_injective
  obtain ⟨e, he⟩ : ∃ e, (c : Polynomial Ω).coeff e ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Subtype.ext (Polynomial.ext h))
  have hce := (GlobalTheory.T.mem_linearSystemConeAlgebra_iff_coeff K V Ω ev _).1 c.2 e
  refine le_trans ?_ (GlobalTheory.T.rankGrowthLimsup_shift_le D e fun k => hilb ev (a * k))
  refine limsup_le_limsup (Eventually.of_forall fun k => ENNReal.div_le_div_right (mul_le_mul_right
    (ENat.toENNReal_le.2 (Cardinal.toENat.monotone' ?_)) _) _)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
  have key : ∀ t ∈ S k, (c : Polynomial Ω).coeff e ^ (1 + a) * t ∈
      ((LinearMap.range ev) ^ ((1 + a) * (k + e)) : Submodule K Ω) := fun t ht => by
    obtain ⟨h1, n, h, h2, h3, h4⟩ := hS k t ht
    obtain ⟨s, hs⟩ := H _ h1 ⟨⟨_, X_pow_mul_C_mem ev h2⟩, ⟨_, X_pow_mul_C_mem ev h4⟩,
      fun h0 => mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.C_ne_zero.2 h3)
        (congrArg Subtype.val h0), by
        change Polynomial.X ^ n * Polynomial.C h * _ = Polynomial.X ^ _ * Polynomial.C (t * h)
        rw [map_mul, pow_add]; ring⟩
    have h5 := (GlobalTheory.T.mem_linearSystemConeAlgebra_iff_coeff K V Ω ev _).1 s.2 (e + (1 + a) * k)
    have hs' : (s : Polynomial Ω) = (c : Polynomial Ω) * (Polynomial.X ^ ((1 + a) * k) * Polynomial.C t) := hs.symm
    rw [hs', ← mul_assoc, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_pow] at h5
    have h6 := Submodule.mul_mem_mul (Submodule.pow_mem_pow _ hce a) h5
    rw [← pow_mul, ← pow_add] at h6
    rw [show (1 + a) * (k + e) = e * a + (e + (1 + a) * k) by ring, pow_add _ 1 a, pow_one, mul_comm _ (_ ^ a), mul_assoc]
    exact h6
  refine LinearMap.rank_le_of_injective
    ((LinearMap.mulLeft K ((c : Polynomial Ω).coeff e ^ (1 + a))).restrict key) fun x y hxy => ?_
  exact Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ he) (congrArg Subtype.val hxy))

end Quot

theorem isUnit_of_growth {K A B A' : Type} [Field K] [CommRing A] [Algebra K A] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] [CommRing A'] [IsDomain A'] [Algebra B A'] [Algebra.FiniteType B A'] (ι : A →+* A')
    (hinj : Function.Injective (algebraMap B A')) (σ : K →+* ℂ) {n k : ℕ} {w : Fin n → A} {s : A} {C : ℝ}
    (h : ∀ φ : A →+* ℂ, φ.comp (algebraMap K A) = σ → ‖φ s‖ ≤ C * (1 + ∑ i, ‖φ (w i)‖) ^ k)
    (w' : Fin n → B) (u : B) (hK : ∀ c, ι (algebraMap K A c) = algebraMap B A' (algebraMap K B c))
    (hw : ∀ i, ι (w i) = algebraMap B A' (w' i)) (hs : ι s * algebraMap B A' u = 1) : IsUnit u := by
  by_contra hu
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  obtain ⟨q, hq, hext⟩ := GlobalTheory.T.exists_ne_zero_forall_complexPoint_extend' B A' hinj
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_complex_point_norm_lt_of_not_isUnit' K B σ n w' u q hu hq
  obtain ⟨T, hT⟩ : ∃ T, T = |C| * (1 + ∑ _i : Fin n, |M|) ^ k := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  obtain ⟨φ, h1, h2, h3, h4⟩ := hM (1 / (T + 1)) (by positivity)
  obtain ⟨ψ, rfl⟩ := hext φ h2
  have h5 := h (ψ.comp ι) (h1 ▸ RingHom.ext fun c => congrArg ψ (hK c))
  have h6 : ‖ψ (ι s)‖ ≤ T := h5.trans (by
    rw [hT]
    refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ k) (by positivity) (abs_nonneg C)
    refine add_le_add_right (Finset.sum_le_sum fun i _ => ?_) 1
    rw [RingHom.comp_apply, hw]
    exact (h4 i).trans (le_abs_self M))
  have h8 : ‖ψ (ι s)‖ * ‖ψ (algebraMap B A' u)‖ = 1 := by
    rw [← norm_mul, ← map_mul, hs, map_one, norm_one]
  rw [RingHom.comp_apply, lt_div_iff₀ (by positivity)] at h3
  nlinarith [norm_nonneg (ψ (algebraMap B A' u))]

theorem isIntegral_of_isUnit_inv {R L : Type} [CommRing R] [Nontrivial R] [Field L] [Algebra R L] {x : L} (hx : x ≠ 0)
    (hu : IsUnit (⟨x⁻¹, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin R {x⁻¹})) : IsIntegral R x := by
  let _ := invertibleOfNonzero (inv_ne_zero hx)
  obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
    x⁻¹ (⊥ : Ideal R) bot_ne_top (by rw [Ideal.span_singleton_eq_top.2 hu, sup_top_eq])
  rw [invOf_eq_inv, inv_inv] at hpx
  exact ⟨p, sub_eq_zero.1 (Ideal.mem_bot.1 hp), hpx⟩

theorem isIntegral_of_polynomialGrowth_abstract_fractionField {K R A L : Type} [Field K] [CommRing R] [Nontrivial R] [CommRing A] [Field L]
    [Algebra K R] [Algebra K A] [Algebra R A] [Algebra A L] [Algebra R L] [Algebra K L] [IsScalarTower K R A]
    [IsScalarTower R A L] [IsScalarTower K A L] [IsScalarTower K R L] [Algebra.FiniteType K R] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) {n k : ℕ} {w : Fin n → R} {s : A} {C : ℝ}
    (h : ∀ φ : A →+* ℂ, φ.comp (algebraMap K A) = σ → ‖φ s‖ ≤ C * (1 + ∑ i, ‖φ (algebraMap R A (w i))‖) ^ k) :
    IsIntegral R (algebraMap A L s) := by
  rcases eq_or_ne (algebraMap A L s) 0 with h0 | hx0
  · exact h0 ▸ isIntegral_zero
  refine isIntegral_of_isUnit_inv hx0 ?_
  let B := Algebra.adjoin R {(algebraMap A L s)⁻¹}
  let A' := Algebra.adjoin A {(algebraMap A L s)⁻¹}
  have hx : (algebraMap A L s)⁻¹ ∈ A' := Algebra.subset_adjoin rfl
  have hle' : B ≤ A'.restrictScalars R := Algebra.adjoin_le (Set.singleton_subset_iff.2 hx)
  have hle : ∀ x ∈ B, x ∈ A' := fun x hx => hle' hx
  let _ : Algebra B A' := (RingHom.codRestrict B.val.toRingHom A' fun x => hle x x.2).toAlgebra
  have : IsScalarTower K B A' := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K A A', IsScalarTower.algebraMap_apply K R B]
    exact Subtype.ext ((IsScalarTower.algebraMap_apply K A L c).symm.trans (IsScalarTower.algebraMap_apply K R L c))
  have : Algebra.FiniteType R B := .adjoin_of_finite (Set.finite_singleton _)
  have : Algebra.FiniteType A A' := .adjoin_of_finite (Set.finite_singleton _)
  have : Algebra.FiniteType K B := .trans (S := R) inferInstance inferInstance
  have : Algebra.FiniteType K A' := .trans (S := A) inferInstance inferInstance
  have : Algebra.FiniteType B A' := .of_restrictScalars_finiteType K B A'
  exact isUnit_of_growth (B := B) (algebraMap A A') (fun x y hxy => Subtype.ext (congrArg (fun z : A' => (z : L)) hxy)) σ h
    (fun i => algebraMap R B (w i)) _
    (fun c => (IsScalarTower.algebraMap_apply K A A' c).symm.trans (IsScalarTower.algebraMap_apply K B A' c))
    (fun i => Subtype.ext (IsScalarTower.algebraMap_apply R A L _).symm) (Subtype.ext (mul_inv_cancel₀ hx0))

theorem isIntegral_of_growth {K A : Type} [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (n k : ℕ) (w : Fin n → A) (s : A) (C : ℝ)
    (h : ∀ φ : A →+* ℂ, φ.comp (algebraMap K A) = σ → ‖φ s‖ ≤ C * (1 + ∑ i, ‖φ (w i)‖) ^ k) :
    IsIntegral (Algebra.adjoin K (Set.range w)) s := by
  have : Algebra.FiniteType K (Algebra.adjoin K (Set.range w)) := .adjoin_of_finite (Set.finite_range w)
  exact (isIntegral_algebraMap_iff (IsFractionRing.injective A (FractionRing A))).1
    (isIntegral_of_polynomialGrowth_abstract_fractionField (R := Algebra.adjoin K (Set.range w)) (L := FractionRing A) σ (k := k) (C := C)
      (w := fun i => ⟨w i, Algebra.subset_adjoin ⟨i, rfl⟩⟩) h)

theorem degree_growth_integral : (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ δ : ℕ, IsImageDeg ev D δ → growth D (fun k => hilb ev (a * k)) = (a : ℝ≥0∞) ^ D * δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → growth D (fun k => hilb ev (a * k)) ≠ 0 → growth D (fun k => hilb ev (a * k)) ≠ ⊤ → ∃ δ : ℕ, IsImageDeg ev D δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ S : ℕ → Submodule K Ω, (∀ k, ∀ t ∈ S k, IsIntDeg ev (a * k) t ∧ IsRatio ev (a * k) t) → growth D (fun k => Cardinal.toENat (Module.rank K (S k))) ≤ growth D (fun k => hilb ev (a * k))) ∧ (∀ (K A : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ) (n k : ℕ) (w : Fin n → A) (s : A) (C : ℝ), (∀ φ : A →+* ℂ, φ.comp (algebraMap K A) = σ → ‖φ s‖ ≤ C * (1 + ∑ i, ‖φ (w i)‖) ^ k) → IsIntegral (Algebra.adjoin K (Set.range w)) s) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ ev D a ha δ h => growth_hilb_eq ev D a ha δ h,
    fun _ _ _ _ _ _ _ _ _ _ ev D a ha h0 h1 => exists_isImageDeg ev D a ha h0 h1,
    fun _ _ _ _ _ _ _ _ _ _ ev D a ha S hS => growth_rank_le ev D a ha S hS,
    fun _ _ _ _ _ _ _ σ n k w s C h => isIntegral_of_growth σ n k w s C h⟩

end GlobalTheory.ConeDeg
end
