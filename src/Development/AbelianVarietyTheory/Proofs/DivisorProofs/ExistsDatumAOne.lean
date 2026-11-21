import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PlacesOverU
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ThreeNeSqAddSq

section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.Published.LandherrModel Polynomial
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.Gauss

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem hζ : IsPrimitiveRoot ii 4 := IsCyclotomicExtension.zeta_spec 4 ℚ Qi

def pbO : PowerBasis ℤ (𝓞 Qi) := hζ.integralPowerBasis

def ζO : 𝓞 Qi := hζ.toInteger

theorem pbO_gen : pbO.gen = ζO := hζ.integralPowerBasis_gen

theorem pbO_dim : pbO.dim = 2 := by
  rw [pbO, hζ.integralPowerBasis_dim]; decide

theorem coe_ζO : (ζO : Qi) = ii := rfl

theorem ζO_sq : ζO * ζO = -1 := by
  ext; simp [coe_ζO, ii_mul]

theorem coordO (x : 𝓞 Qi) : ∃ a b : ℤ, x = a + b * ζO := by
  obtain ⟨f, hf, rfl⟩ := pbO.exists_eq_aeval x
  rw [pbO_dim] at hf
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)]
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  simp [pbO_gen]; ring

theorem minpoly_ζO : minpoly ℤ pbO.gen = cyclotomic 4 ℤ := by
  rw [pbO_gen, ← RingOfIntegers.minpoly_coe, coe_ζO]
  exact (cyclotomic_eq_minpoly hζ (by norm_num)).symm

theorem cyc4 (R : Type) [CommRing R] : cyclotomic 4 R = 1 + X ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ]

def red : 𝓞 Qi →+* ZMod 5 :=
  (pbO.lift (2 : ZMod 5) (by rw [minpoly_ζO, cyc4]; simp; decide)).toRingHom

theorem red_ζO : red ζO = 2 := by
  simp [red, ← pbO_gen]

theorem red_coord (a b : ℤ) : red (a + b * ζO) = a + 2 * b := by
  simp [red_ζO]; ring

theorem red_surj : Function.Surjective red := by
  intro y
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
  exact ⟨n, by simp⟩

def u : HeightOneSpectrum (𝓞 Qi) where
  asIdeal := RingHom.ker red
  isPrime := (RingHom.ker_isMaximal_of_surjective red red_surj).isPrime
  ne_bot := by
    intro h
    have h5 : (5 : 𝓞 Qi) ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_ofNat]; decide
    rw [h, Ideal.mem_bot] at h5
    norm_num at h5

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

abbrev cO : 𝓞 Qi →+* 𝓞 Qi := (IsCMField.ringOfIntegersComplexConj Qi : 𝓞 Qi →+* 𝓞 Qi)

theorem cO_ζO : IsCMField.ringOfIntegersComplexConj Qi ζO = -ζO := by
  ext; simp [IsCMField.coe_ringOfIntegersComplexConj, coe_ζO, cc_ii]

theorem red_cO_coord (a b : ℤ) : red (cO (a + b * ζO)) = a - 2 * b := by
  simp [cO_ζO, red_ζO]; ring

theorem mem_u {x : 𝓞 Qi} : x ∈ u.asIdeal ↔ red x = 0 := RingHom.mem_ker

theorem five_eq : ((5 : ℕ) : 𝓞 Qi) = (2 - ζO) * (2 + ζO) := by
  push_cast; linear_combination ζO_sq

theorem red_two_sub : red (2 - ζO) = 0 := by
  rw [map_sub, map_ofNat, red_ζO, sub_self]

theorem red_cO_two_add : red (cO (2 + ζO)) = 0 := by
  rw [map_add, map_ofNat, cO, RingHom.coe_coe, cO_ζO, map_add, map_neg, map_ofNat, red_ζO, add_neg_cancel]

theorem red_cO_two_sub : red (cO (2 - ζO)) = 4 := by
  rw [map_sub, map_ofNat, cO, RingHom.coe_coe, cO_ζO, map_sub, map_neg, map_ofNat, red_ζO]; decide

theorem u_split : u.asIdeal * u.asIdeal.comap cO = Ideal.span {((5 : ℕ) : 𝓞 Qi)} := by
  apply le_antisymm
  · intro x hx
    have h1 := Ideal.mul_le_inf hx
    rw [Ideal.mem_inf, Ideal.mem_comap, mem_u, mem_u] at h1
    obtain ⟨a, b, rfl⟩ := coordO x
    rw [red_coord, red_cO_coord] at h1
    obtain ⟨h1, h2⟩ := h1
    have h5 : (5 : ZMod 5) = 0 := by decide
    have ha : ((a : ℤ) : ZMod 5) = 0 := by linear_combination 3 * h1 + 3 * h2 - (a : ZMod 5) * h5
    have hb : ((b : ℤ) : ZMod 5) = 0 := by linear_combination 4 * h1 - 4 * h2 - 3 * (b : ZMod 5) * h5
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [Ideal.mem_span_singleton]
    exact ⟨a' + b' * ζO, by push_cast; ring⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, five_eq]
    apply Ideal.mul_mem_mul
    · rw [mem_u]; exact red_two_sub
    · rw [Ideal.mem_comap, mem_u]; exact red_cO_two_add

theorem u_split_ne : u.asIdeal.comap cO ≠ u.asIdeal := by
  intro h
  have h1 : (2 - ζO) ∈ u.asIdeal := by rw [mem_u]; exact red_two_sub
  rw [← h, Ideal.mem_comap, mem_u, red_cO_two_sub] at h1
  revert h1; decide

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

theorem finrank_Qi : Module.finrank ℚ Qi = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Qi (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

theorem coord_zero {a b : ℚ} (h : (a : Qi) + b * ii = 0) : a = 0 ∧ b = 0 := by
  have h2 : ((a ^ 2 + b ^ 2 : ℚ) : Qi) = 0 := by
    push_cast
    linear_combination ((a : Qi) - b * ii) * h + (b : Qi) ^ 2 * ii_mul
  have h3 : a ^ 2 + b ^ 2 = 0 := by exact_mod_cast h2
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem li : LinearIndependent ℚ ![(1 : Qi), ii] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  apply coord_zero
  simpa [Algebra.smul_def] using hst

def bQ : Module.Basis (Fin 2) ℚ Qi :=
  basisOfLinearIndependentOfCardEqFinrank li (by rw [finrank_Qi]; simp)

theorem bQ_zero : bQ 0 = 1 := by simp [bQ]
theorem bQ_one : bQ 1 = ii := by simp [bQ]

theorem trace_ii : Algebra.trace ℚ Qi ii = 0 := by
  rw [Algebra.trace_eq_matrix_trace bQ, Matrix.trace_fin_two, Algebra.leftMulMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have e1 : Algebra.lmul ℚ Qi ii (bQ 0) = bQ 1 := by simp [bQ_zero, bQ_one]
  have e2 : Algebra.lmul ℚ Qi ii (bQ 1) = -bQ 0 := by simp [bQ_zero, bQ_one, ii_mul]
  rw [e1, e2, map_neg, bQ.repr_self, bQ.repr_self]; simp

theorem trace_coord (a b : ℚ) : Algebra.trace ℚ Qi ((a : Qi) + b * ii) = 2 * a := by
  have ha : (a : Qi) = algebraMap ℚ Qi a := (eq_ratCast _ a).symm
  have hb : (b : Qi) = algebraMap ℚ Qi b := (eq_ratCast _ b).symm
  rw [map_add, ha, hb, ← Algebra.smul_def, map_smul, trace_ii, smul_zero, add_zero,
    Algebra.trace_algebraMap, finrank_Qi, nsmul_eq_mul]; norm_num

theorem cc_coord (a b : ℚ) : IsCMField.complexConj Qi ((a : Qi) + b * ii) = a - b * ii := by
  simp [map_add, map_mul, map_ratCast, cc_ii]; ring

@[instance_reducible] def starQi : StarRing Qi where
  star := IsCMField.complexConj Qi
  star_involutive := IsCMField.complexConj_apply_apply Qi
  star_mul x y := by rw [map_mul, mul_comm]
  star_add x y := map_add _ x y

attribute [local instance] starQi

theorem star_eq (x : Qi) : star x = IsCMField.complexConj Qi x := rfl

def ψ : LinearMap.BilinForm ℚ Qi :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ Qi (-ii / 2 * x * IsCMField.complexConj Qi y))
    (fun x x' y => by simp only [mul_add, add_mul, map_add])
    (fun r x y => by rw [mul_smul_comm, smul_mul_assoc, map_smul])
    (fun x y y' => by simp only [map_add, mul_add])
    (fun r x y => by rw [map_rat_smul, mul_smul_comm, map_smul])

theorem ψ_apply (x y : Qi) : ψ x y = Algebra.trace ℚ Qi (-ii / 2 * x * IsCMField.complexConj Qi y) := rfl

theorem ψ_coord (a b c d : ℚ) : ψ ((a : Qi) + b * ii) ((c : Qi) + d * ii) = b * c - a * d := by
  rw [ψ_apply, cc_coord]
  have : -ii / 2 * ((a : Qi) + b * ii) * ((c : Qi) - d * ii) =
      (((b * c - a * d) / 2 : ℚ) : Qi) + ((-(a * c + b * d) / 2 : ℚ) : Qi) * ii := by
    push_cast
    linear_combination (-((b : Qi) * c - a * d) / 2 + (b : Qi) * d * ii / 2) * ii_mul
  rw [this, trace_coord]; ring

theorem ψ_alt (x : Qi) : ψ x x = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_coord x
  rw [ψ_coord]; ring

theorem ψ_adj (b x y : Qi) : ψ (b * x) y = ψ x (star b * y) := by
  rw [ψ_apply, ψ_apply, star_eq, map_mul (IsCMField.complexConj Qi), IsCMField.complexConj_apply_apply]
  congr 1; ring

theorem pos (x : Qi) (hx : x ≠ 0) :
    0 < LinearMap.trace ℚ Qi (LinearMap.mulLeft ℚ (x * star x)) := by
  change 0 < Algebra.trace ℚ Qi (x * star x)
  obtain ⟨a, b, rfl⟩ := exists_coord x
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩; simp at hx
  have : ((a : Qi) + b * ii) * star ((a : Qi) + b * ii) = ((a ^ 2 + b ^ 2 : ℚ) : Qi) + ((0 : ℚ) : Qi) * ii := by
    rw [star_eq, cc_coord]; push_cast; linear_combination (-(b : Qi) ^ 2) * ii_mul
  rw [this, trace_coord]
  by_cases ha : a = 0
  · have hb : b ≠ 0 := fun hb => hab ⟨ha, hb⟩
    positivity
  · positivity

theorem exists_τ : ∃ τ : Qi →+* ℂ, τ ii = Complex.I := by
  let σ : Qi →+* ℂ := Classical.choice inferInstance
  have h : σ ii * σ ii = -1 := by rw [← map_mul, ii_mul]; simp
  have h' : σ ii = Complex.I ∨ σ ii = -Complex.I := by
    rw [← mul_self_eq_mul_self_iff, h]; simp
  rcases h' with h' | h'
  · exact ⟨σ, h'⟩
  · exact ⟨(starRingEnd ℂ).comp σ, by simp [h']⟩

def τ₀ : Qi →+* ℂ := exists_τ.choose

theorem τ₀_ii : τ₀ ii = Complex.I := exists_τ.choose_spec

theorem τ₀_coord (a b : ℚ) : τ₀ ((a : Qi) + b * ii) = ⟨a, b⟩ := by
  apply Complex.ext <;> simp [τ₀_ii]

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

attribute [local instance] starQi

theorem mem_bot_iff (x : Qi) : x ∈ (⊥ : Subalgebra (𝓞 Qi) Qi) ↔ ∃ a b : ℤ, x = a + b * ii := by
  rw [Algebra.mem_bot]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨a, b, rfl⟩ := coordO y
    exact ⟨a, b, by simp [coe_ζO]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a + b * ζO, by simp [coe_ζO]⟩

theorem mem_bot_of_isIntegral {x : Qi} (hx : IsIntegral ℤ x) : x ∈ (⊥ : Subalgebra (𝓞 Qi) Qi) :=
  Algebra.mem_bot.2 ⟨⟨x, hx⟩, rfl⟩

def Λ : Submodule ℤ Qi := Submodule.span ℤ (Set.range ![(1 : Qi), ii])

theorem mem_Λ (x : Qi) : x ∈ Λ ↔ ∃ a b : ℤ, x = a + b * ii := by
  rw [Λ, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c 0, c 1, by simp [Fin.sum_univ_two]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨![a, b], by simp [Fin.sum_univ_two]⟩

theorem Λ_eq : (Subalgebra.toSubmodule (⊥ : Subalgebra (𝓞 Qi) Qi)).restrictScalars ℤ = Λ := by
  ext x
  rw [Submodule.restrictScalars_mem, Subalgebra.mem_toSubmodule, mem_bot_iff, mem_Λ]

theorem liZ : LinearIndependent ℤ ![(1 : Qi), ii] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h := coord_zero (a := s) (b := t) (by push_cast; simpa [zsmul_eq_mul] using hst)
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

def bΛ : Module.Basis (Fin 2) ℤ Λ := Module.Basis.span liZ

theorem coe_bΛ (i : Fin 2) : (bΛ i : Qi) = ![(1 : Qi), ii] i :=
  congrArg Subtype.val (Module.Basis.span_apply liZ i)

theorem coe_eq_repr (x : Λ) : (x : Qi) = ((bΛ.repr x 0 : ℤ) : Qi) + ((bΛ.repr x 1 : ℤ) : Qi) * ii := by
  have h := congrArg Subtype.val (bΛ.sum_repr x)
  rw [← h]
  simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, coe_bΛ, zsmul_eq_mul]
  simp

def E : LinearMap.BilinForm ℤ Λ :=
  LinearMap.mk₂ ℤ (fun x y => bΛ.repr x 1 * bΛ.repr y 0 - bΛ.repr x 0 * bΛ.repr y 1)
    (fun x x' y => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)

theorem E_apply (x y : Λ) : E x y = bΛ.repr x 1 * bΛ.repr y 0 - bΛ.repr x 0 * bΛ.repr y 1 := rfl

theorem E_eq (x y : Λ) : ((E x y : ℤ) : ℚ) = ψ x y := by
  rw [coe_eq_repr x, coe_eq_repr y, E_apply]
  have := ψ_coord (bΛ.repr x 0) (bΛ.repr x 1) (bΛ.repr y 0) (bΛ.repr y 1)
  push_cast at this ⊢
  rw [this]

theorem bijective_of_gram {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 2) R M) (B : LinearMap.BilinForm R M) (h00 : B (b 0) (b 0) = 0)
    (h01 : B (b 0) (b 1) = -1) (h10 : B (b 1) (b 0) = 1) (h11 : B (b 1) (b 1) = 0) :
    Function.Bijective B := by
  have key : ∀ m j, B m (b j) = b.repr m 0 * B (b 0) (b j) + b.repr m 1 * B (b 1) (b j) := by
    intro m j
    conv_lhs => rw [← b.sum_repr m]
    simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · intro m m' h
    have e0 := key m 0
    have e1 := key m 1
    have e0' := key m' 0
    have e1' := key m' 1
    rw [h] at e0 e1
    rw [h00, h10] at e0 e0'
    rw [h01, h11] at e1 e1'
    apply b.repr.injective
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linear_combination e1 - e1'
    · simp only [Fin.mk_one, Fin.isValue]; linear_combination e0' - e0
  · intro f
    refine ⟨-(f (b 1)) • b 0 + f (b 0) • b 1, b.ext fun j => ?_⟩
    fin_cases j <;> simp [h00, h01, h10, h11]

theorem E_bΛ (i j : Fin 2) : E (bΛ i) (bΛ j) = ![![0, -1], ![1, 0]] i j := by
  rw [E_apply]
  fin_cases i <;> fin_cases j <;> simp [Module.Basis.repr_self, Finsupp.single_apply]

theorem E_perfect : Function.Bijective (E.baseChange ℤ_[5]) := by
  let b := Algebra.TensorProduct.basis ℤ_[5] bΛ
  have hb : ∀ i j, E.baseChange ℤ_[5] (b i) (b j) = ((![![0, -1], ![1, 0]] i j : ℤ) : ℤ_[5]) := by
    intro i j
    simp only [b, Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul, E_bΛ, mul_one,
      zsmul_eq_mul]
  refine bijective_of_gram b _ ?_ ?_ ?_ ?_ <;> rw [hb] <;> simp

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.Gauss

attribute [local instance] starQi

def c : ℂ := ((Real.sqrt (1 / 2) : ℝ) : ℂ)

theorem c_ne : c ≠ 0 := by
  simp [c]

theorem c_sq : c * (starRingEnd ℂ) c = 1 / 2 := by
  rw [c, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

def P : GL (Fin 1) ℂ :=
  ⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul_comm, mul_inv_cancel₀ c_ne, one_mul, one_smul],
    by rw [smul_mul_smul_comm, inv_mul_cancel₀ c_ne, one_mul, one_smul]⟩

def hmat : Matrix (Fin 1) (Fin 1) ℂ :=
  (P : Matrix (Fin 1) (Fin 1) ℂ) * diagonal (fun k : Fin 1 => if (k : ℕ) < 1 then (1 : ℂ) else -1) *
    (P : Matrix (Fin 1) (Fin 1) ℂ)ᴴ

theorem hmat_apply : hmat 0 0 = 1 / 2 := by
  simp [hmat, P, Matrix.mul_apply, c_sq]

theorem embOver_self : embOver Qi Qi (τ₀.comp (algebraMap Qi Qi)) = {τ₀} := by
  ext τ; simp [embOver, Algebra.algebraMap_self]

def ρ (τ : Qi →+* ℂ) : Qi →+* Matrix (Fin 1) (Fin 1) ℂ := (Matrix.scalar (Fin 1) : ℂ →+* _).comp τ

open Classical in
theorem sig : ∃ (ρ : (Qi →+* ℂ) → Qi →+* Matrix (Fin 1) (Fin 1) ℂ) (h : (Qi →+* ℂ) → Matrix (Fin 1) (Fin 1) ℂ),
    (∀ τ a, ρ τ (algebraMap Qi Qi a) = Matrix.scalar (Fin 1) (τ a)) ∧
    (∀ τ b, ρ τ (star b) = (ρ τ b)ᴴ) ∧
    (∀ τ ∈ embOver Qi Qi (τ₀.comp (algebraMap Qi Qi)), HermSig (h τ) (if τ = τ₀ then 1 else 0)) ∧
    ∀ x y, ((ψ x y : ℚ) : ℝ) =
      ∑ τ ∈ embOver Qi Qi (τ₀.comp (algebraMap Qi Qi)), 2 * (trace (ρ τ x * h τ * (ρ τ y)ᴴ)).im := by
  refine ⟨ρ, fun _ => hmat, fun τ a => rfl, fun τ b => ?_, fun τ hτ => ?_, fun x y => ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp [ρ, star_eq, IsCMField.complexEmbedding_complexConj]
  · rw [embOver_self, Finset.mem_singleton] at hτ
    rw [if_pos hτ]
    exact ⟨le_rfl, P, rfl⟩
  · rw [embOver_self, Finset.sum_singleton]
    obtain ⟨a, b, rfl⟩ := exists_coord x
    obtain ⟨c', d, rfl⟩ := exists_coord y
    rw [ψ_coord]
    simp only [ρ, RingHom.coe_comp, Function.comp_apply, τ₀_coord, Matrix.trace_fin_one, Matrix.mul_apply,
      Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, Matrix.conjTranspose_apply, hmat_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    simp [Complex.mul_im, Complex.mul_re]
    push_cast; ring

def m1 (A : Type) [CommRing A] : A ≃ₐ[A] Matrix (Fin 1) (Fin 1) A :=
  AlgEquiv.ofBijective (Algebra.ofId A _)
    ⟨fun a b h => by simpa [Matrix.algebraMap_eq_diagonal] using congrFun (congrFun h 0) 0,
     fun M => ⟨M 0 0, by ext i j; fin_cases i; fin_cases j; simp [Matrix.algebraMap_eq_diagonal]⟩⟩

def splitW : u.adicCompletionIntegers Qi ⊗[𝓞 Qi] (⊥ : Subalgebra (𝓞 Qi) Qi) ≃ₐ[u.adicCompletionIntegers Qi]
    Matrix (Fin 1) (Fin 1) (u.adicCompletionIntegers Qi) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
      (Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective (𝓞 Qi) Qi))).trans
    ((Algebra.TensorProduct.rid (𝓞 Qi) _ _).trans (m1 _))

theorem OB_max (O : Subring Qi) (hO : ((⊥ : Subalgebra (𝓞 Qi) Qi) : Set Qi) ⊆ O) (hfg : O.toAddSubgroup.FG)
    (x : Qi) (hx : x ∈ O) : ∃ m : ℕ, m.Coprime 5 ∧ (m : Qi) * x ∈ (⊥ : Subalgebra (𝓞 Qi) Qi) := by
  refine ⟨1, Nat.coprime_one_left 5, ?_⟩
  rw [Nat.cast_one, one_mul]
  apply mem_bot_of_isIntegral
  refine IsIntegral.of_mem_of_fg (subalgebraOfSubring O) ?_ x (mem_subalgebraOfSubring.2 hx)
  rw [Submodule.fg_iff_addSubgroup_fg]
  exact hfg

theorem OB_span : Submodule.span ℚ ((⊥ : Subalgebra (𝓞 Qi) Qi) : Set Qi) = ⊤ := by
  rw [eq_top_iff, ← bQ.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  rw [SetLike.mem_coe, mem_bot_iff]
  fin_cases i
  · exact ⟨1, 0, by simp [bQ_zero]⟩
  · exact ⟨0, 1, by simp [bQ_one]⟩

theorem OB_star (x : Qi) (hx : x ∈ (⊥ : Subalgebra (𝓞 Qi) Qi)) : star x ∈ (⊥ : Subalgebra (𝓞 Qi) Qi) := by
  obtain ⟨a, b, rfl⟩ := (mem_bot_iff x).1 hx
  rw [mem_bot_iff, star_eq]
  refine ⟨a, -b, ?_⟩
  have := cc_coord a b
  push_cast at this ⊢
  rw [this]; ring

end GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT

open Gauss

attribute [local instance] Gauss.starQi

def gaussDatum : HTDatum Qi Qi 5 where
  quad := finrank_Qi
  u := Gauss.u
  split := u_split
  split_ne := u_split_ne
  w := Gauss.u
  w_over := by
    ext x
    rw [Ideal.mem_comap]
    exact Iff.rfl
  τ₀ := Gauss.τ₀
  B := Qi
  starB := starQi
  n := 1
  n_pos := one_pos
  dim := by simp
  star_F := fun _ => rfl
  pos := Gauss.pos
  OB := ⊥
  OB_fg := by rw [Λ_eq]; exact Submodule.fg_span (Set.finite_range _)
  OB_span := OB_span
  OB_star := OB_star
  OB_max := OB_max
  splitW := Gauss.splitW
  ψ := Gauss.ψ
  alt := ψ_alt
  adj := ψ_adj
  sig := Gauss.sig
  Λ := Gauss.Λ
  Λ_fg := Submodule.fg_span (Set.finite_range _)
  Λ_span := by rw [← Λ_eq]; exact OB_span
  Λ_stable := by
    intro b hb x hx
    rw [← Λ_eq] at hx ⊢
    exact Subalgebra.mul_mem _ hb hx
  E := Gauss.E
  E_eq := Gauss.E_eq
  perfect := E_perfect

example : gaussDatum.n = 1 := rfl

example : gaussDatum.IsDivision := fun x hx => (isUnit_iff_ne_zero (G₀ := Qi)).2 hx

end GlobalTheory.UPel.HT
end
end

section
noncomputable section
open NumberField
open scoped TensorProduct ComplexConjugate
open GlobalTheory.Published.LandherrModel GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.GaussOne

theorem liO : LinearIndependent ℤ ![(1 : 𝓞 Qi), ζO] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h := congrArg (algebraMap (𝓞 Qi) Qi) hst
  simp at h
  rw [show algebraMap (𝓞 Qi) Qi ζO = ii from coe_ζO] at h
  have h2 := coord_zero (a := s) (b := t) (by push_cast; exact h)
  exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩

theorem spanO : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 Qi), ζO]) := by
  intro x _
  obtain ⟨a, b, rfl⟩ := coordO x
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨![a, b], by simp [Fin.sum_univ_two, zsmul_eq_mul]⟩

def bO : Module.Basis (Fin 2) ℤ (𝓞 Qi) := Module.Basis.mk liO spanO

theorem bO_zero : bO 0 = 1 := by simp [bO]
theorem bO_one : bO 1 = ζO := by simp [bO]

theorem repr_coord (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) = Finsupp.equivFunOnFinite.symm ![a, b] := by
  have : ((a : 𝓞 Qi) + b * ζO) = a • bO 0 + b • bO 1 := by simp [bO_zero, bO_one, zsmul_eq_mul]
  rw [this, map_add, map_zsmul, map_zsmul, bO.repr_self, bO.repr_self]
  ext i; fin_cases i <;> simp

theorem repr0 (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) 0 = a := by simp [repr_coord]
theorem repr1 (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) 1 = b := by simp [repr_coord]

def barO : 𝓞 Qi ≃+* 𝓞 Qi := (IsCMField.ringOfIntegersComplexConj Qi).toRingEquiv

theorem barO_apply (x : 𝓞 Qi) : barO x = IsCMField.ringOfIntegersComplexConj Qi x := rfl

theorem barO_eq (x : 𝓞 Qi) : ((barO x : 𝓞 Qi) : Qi) = IsCMField.complexConj Qi (x : Qi) := by
  rw [barO_apply, IsCMField.coe_ringOfIntegersComplexConj]

theorem barO_barO (x : 𝓞 Qi) : barO (barO x) = x := by
  ext; rw [barO_eq, barO_eq, IsCMField.complexConj_apply_apply]

theorem barO_ζO : barO ζO = -ζO := cO_ζO

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT.GaussOne

def EF : LinearMap.BilinForm ℤ (𝓞 Qi) :=
  LinearMap.mk₂ ℤ (fun x y => bO.repr x 1 * bO.repr y 0 - bO.repr x 0 * bO.repr y 1)
    (fun x x' y => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)

theorem EF_coord (a b c d : ℤ) : EF ((a : 𝓞 Qi) + b * ζO) ((c : 𝓞 Qi) + d * ζO) = b * c - a * d := by
  simp only [EF, LinearMap.mk₂_apply, repr0, repr1]

theorem mul_coord (a b c d : ℤ) : ((a : 𝓞 Qi) + b * ζO) * ((c : 𝓞 Qi) + d * ζO) =
    ((a * c - b * d : ℤ) : 𝓞 Qi) + ((a * d + b * c : ℤ) : 𝓞 Qi) * ζO := by
  push_cast; linear_combination (b * d : 𝓞 Qi) * ζO_sq

theorem bar_coord (a b : ℤ) : barO ((a : 𝓞 Qi) + b * ζO) = ((a : ℤ) : 𝓞 Qi) + ((-b : ℤ) : 𝓞 Qi) * ζO := by
  simp [barO_ζO]

theorem EF_alt (x : 𝓞 Qi) : EF x x = 0 := by
  obtain ⟨a, b, rfl⟩ := coordO x
  rw [EF_coord]; ring

theorem EF_adj (b x y : 𝓞 Qi) : EF (b * x) y = EF x (barO b * y) := by
  obtain ⟨a, a', rfl⟩ := coordO b
  obtain ⟨c, c', rfl⟩ := coordO x
  obtain ⟨d, d', rfl⟩ := coordO y
  rw [bar_coord, mul_coord, mul_coord, EF_coord, EF_coord]; ring

theorem EF_bO (i j : Fin 2) : EF (bO i) (bO j) = ![![0, -1], ![1, 0]] i j := by
  simp only [EF, LinearMap.mk₂_apply]
  fin_cases i <;> fin_cases j <;> simp [Module.Basis.repr_self, Finsupp.single_apply]

theorem EF_bij : Function.Bijective EF :=
  bijective_of_gram bO EF (by rw [EF_bO]; rfl) (by rw [EF_bO]; rfl) (by rw [EF_bO]; rfl) (by rw [EF_bO]; rfl)

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT.GaussOne

theorem ζ_mul_coord (c d : ℤ) : ζO * ((c : 𝓞 Qi) + d * ζO) = ((-d : ℤ) : 𝓞 Qi) + ((c : ℤ) : 𝓞 Qi) * ζO := by
  push_cast; linear_combination (d : 𝓞 Qi) * ζO_sq

theorem bO_zero' : bO 0 = ((1 : ℤ) : 𝓞 Qi) + ((0 : ℤ) : 𝓞 Qi) * ζO := by simp [bO_zero]
theorem bO_one' : bO 1 = ((0 : ℤ) : 𝓞 Qi) + ((1 : ℤ) : 𝓞 Qi) * ζO := by simp [bO_one]

theorem EF_ζ_bO (i j : Fin 2) : EF (ζO * bO i) (bO j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, bO_zero', bO_one', ζ_mul_coord, EF_coord] <;> norm_num

theorem EF_ζ (x y : 𝓞 Qi) : EF (ζO * x) (ζO * y) = EF x y := by
  rw [EF_adj, ← mul_assoc, barO_ζO, neg_mul, ζO_sq, neg_neg, one_mul]

theorem trace_mulLeft (a b : ℤ) :
    LinearMap.trace ℤ (𝓞 Qi) (LinearMap.mulLeft ℤ ((a : 𝓞 Qi) + b * ζO)) = 2 * a := by
  rw [LinearMap.trace_eq_matrix_trace ℤ bO, Matrix.trace_fin_two, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, bO_zero', bO_one', mul_coord,
    mul_coord, repr0, repr1]
  ring

def bR : Module.Basis (Fin 2) ℝ (ℝ ⊗[ℤ] 𝓞 Qi) := Algebra.TensorProduct.basis ℝ bO

theorem bR_apply (i : Fin 2) : bR i = 1 ⊗ₜ bO i := Algebra.TensorProduct.basis_apply _ _

def J : ℝ ⊗[ℤ] 𝓞 Qi →ₗ[ℝ] ℝ ⊗[ℤ] 𝓞 Qi := (LinearMap.mulLeft ℤ ζO).baseChange ℝ

theorem A_eq (b : 𝓞 Qi) (A : ℝ ⊗[ℤ] 𝓞 Qi →ₗ[ℝ] ℝ ⊗[ℤ] 𝓞 Qi) (h : ∀ x : 𝓞 Qi, A (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) :
    A = (LinearMap.mulLeft ℤ b).baseChange ℝ :=
  bR.ext fun i => by rw [bR_apply, h, LinearMap.baseChange_tmul, LinearMap.mulLeft_apply, smul_eq_mul]

theorem J_J (x : ℝ ⊗[ℤ] 𝓞 Qi) : J (J x) = -x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [J, ← mul_assoc, ζO_sq, TensorProduct.tmul_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy, neg_add]

theorem J_EF (x y : ℝ ⊗[ℤ] 𝓞 Qi) : EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y := by
  have key : (EF.baseChange ℝ).compl₁₂ J J = EF.baseChange ℝ :=
    LinearMap.BilinForm.ext_basis bR fun i j => by
      rw [LinearMap.compl₁₂_apply, bR_apply, bR_apply, J, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, EF_ζ]
  exact LinearMap.congr_fun₂ key x y

theorem J_pos (x : ℝ ⊗[ℤ] 𝓞 Qi) (hx : x ≠ 0) : 0 < EF.baseChange ℝ (J x) x := by
  have hG : ∀ i j, EF.baseChange ℝ (J (bR i)) (bR j) = if i = j then 1 else 0 := by
    intro i j
    rw [bR_apply, bR_apply, J, LinearMap.baseChange_tmul, LinearMap.mulLeft_apply,
      LinearMap.BilinForm.baseChange_tmul, EF_ζ_bO]
    split_ifs <;> simp
  have hx' := bR.sum_repr x
  rw [Fin.sum_univ_two] at hx'
  have hne : ¬ (bR.repr x 0 = 0 ∧ bR.repr x 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hx
    rw [← hx', h0, h1, zero_smul, zero_smul, add_zero]
  rw [← hx']
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hG]
  simp only [Fin.isValue, ite_true, show ((0 : Fin 2) = 1) = False by decide, show ((1 : Fin 2) = 0) = False by decide,
    ite_false, mul_one, mul_zero, add_zero, zero_add]
  by_cases h0 : bR.repr x 0 = 0
  · have h1 : bR.repr x 1 ≠ 0 := fun h1 => hne ⟨h0, h1⟩
    nlinarith [mul_self_pos.2 h1, h0]
  · nlinarith [mul_self_pos.2 h0, mul_self_nonneg (bR.repr x 1)]

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT.GaussOne

theorem emb_ext (τ σ : Qi →+* ℂ) (h : τ ii = σ ii) : τ = σ :=
  RingHom.ext fun x => by
    obtain ⟨a, b, rfl⟩ := exists_coord x
    simp only [map_add, map_mul, map_ratCast, h]

theorem filt : Finset.univ.filter (fun τ : Qi →+* ℂ => τ ((ζO : 𝓞 Qi) : Qi) = (starRingEnd ℂ) Complex.I) =
    {(starRingEnd ℂ).comp τ₀} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    apply emb_ext
    rw [← coe_ζO, h, RingHom.comp_apply, coe_ζO, τ₀_ii]
  · rintro rfl
    show (starRingEnd ℂ) (τ₀ (ζO : Qi)) = _
    rw [coe_ζO, τ₀_ii]

theorem τ₀_int (a b : ℤ) : τ₀ (((a : 𝓞 Qi) + b * ζO : 𝓞 Qi) : Qi) = (a : ℂ) + b * Complex.I := by
  have : (((a : 𝓞 Qi) + b * ζO : 𝓞 Qi) : Qi) = (a : Qi) + b * ii := by
    rw [← coe_ζO]; push_cast; rfl
  rw [this]; simp [τ₀_ii]

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT

open GaussOne

instance fact5' : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def gaussOneDatum : Datum 5 where
  F := Qi
  cm := cm
  bar := barO
  bar_eq := barO_eq
  ω := ζO
  tr := 0
  nm := 1
  tr_eq := by rw [barO_ζO]; simp
  nm_eq := by rw [barO_ζO, mul_neg, ζO_sq]; simp
  disc_neg := by norm_num
  disc_p := by norm_num
  split := ⟨2, by norm_num⟩
  O := 𝓞 Qi
  freeO := inferInstance
  finO := inferInstance
  m := 1
  m_pos := one_pos
  rankO := by rw [one_pow, one_mul]; exact RingOfIntegers.rank Qi
  central := fun x _ => ⟨x, 1, one_ne_zero, by simp⟩
  star := barO.trans (RingEquiv.toOpposite (𝓞 Qi))
  star_star := fun x => by simp [barO_barO]
  star_F := fun c => by simp
  splitP := ⟨(m1 _).restrictScalars (𝓞 Qi)⟩
  La := 𝓞 Qi
  freeLa := inferInstance
  finLa := inferInstance
  n := 1
  n_pos := le_rfl
  rankLa := by rw [one_mul, one_mul]; exact RingOfIntegers.rank Qi
  EF := EF
  alt := EF_alt
  nondeg := EF_bij.1
  perfP := ⟨1, Nat.coprime_one_left 5, fun f => by
    obtain ⟨x, hx⟩ := EF_bij.2 f
    exact ⟨x, by rw [hx, one_smul]⟩⟩
  adj := fun b x y => by simpa using EF_adj b x y
  a := 1
  ρc := Complex.I
  ρc_root := by simp
  tau := ⟨fun _ => τ₀, fun i j _ => Subsingleton.elim i j⟩
  tau_ω := fun _ => by
    show τ₀ (ζO : Qi) = Complex.I
    rw [coe_ζO, τ₀_ii]
  dom := by
    refine ⟨J, J_J, J_EF, J_pos, ?_, ?_⟩
    · intro b A hA
      rw [A_eq b A hA, J, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      exact LinearMap.ext fun y => by simp [mul_left_comm]
    · intro c A hA
      have hA' : ∀ x : 𝓞 Qi, A (1 ⊗ₜ x) = 1 ⊗ₜ (c • x) := by simpa using hA
      rw [A_eq c A hA', J, ← LinearMap.baseChange_comp, ← LinearMap.mulLeft_mul, LinearMap.trace_baseChange,
        LinearMap.trace_baseChange]
      obtain ⟨a, b, rfl⟩ := coordO c
      rw [ζ_mul_coord, trace_mulLeft, trace_mulLeft]
      intro S
      have hS : S = (a : ℂ) + b * Complex.I := by
        simp only [S, Nat.cast_one, one_mul, Finset.univ_unique, Finset.sum_singleton, filt]
        show τ₀ _ + (starRingEnd ℂ) (τ₀ _) - (starRingEnd ℂ) (τ₀ _) = _
        rw [add_sub_cancel_right, τ₀_int]
      rw [hS]
      simp

theorem exists_datum_a_one : ∃ (_ : Fact (Nat.Prime 5)) (D : Datum 5), D.a = 1 ∧ D.n = 1 ∧ D.m = 1 :=
  ⟨fact5', gaussOneDatum, rfl, rfl, rfl⟩

end GlobalTheory.UPel.HT
end
end
