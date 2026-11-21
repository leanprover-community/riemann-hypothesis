import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoPoissonSummationFractionalIdeal

section
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem X_sq_add_one_ne_zero : (X ^ 2 + 1 : F[X]) ≠ 0 := Monic.ne_zero (by monicity!)

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!

def basisOneI : Module.Basis (Fin 2) F (Ext F) :=
  (AdjoinRoot.powerBasis (X_sq_add_one_ne_zero F)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_sq_add_one]))

theorem basisOneI_apply (j : Fin 2) : basisOneI F j = ii F ^ (j : ℕ) := by
  simp [basisOneI, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, ii]

theorem basisOneI_zero : basisOneI F 0 = 1 := by simp [basisOneI_apply]
theorem basisOneI_one : basisOneI F 1 = ii F := by simp [basisOneI_apply]

theorem gEmb_eq (a b : F) : gEmb F (a, b) = a • basisOneI F 0 + b • basisOneI F 1 := by
  simp [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def]

theorem gEmb_mul_ii (a b : F) : gEmb F (a, b) * ii F = (-b) • basisOneI F 0 + a • basisOneI F 1 := by
  simp only [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def, map_neg]
  linear_combination (algebraMap F (Ext F) b) * ii_sq F

theorem norm_gEmb_F (a b : F) : Algebra.norm F (gEmb F (a, b)) = a ^ 2 + b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (basisOneI F), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [basisOneI_zero, mul_one, basisOneI_one, gEmb_mul_ii, gEmb_eq]
  simp [Module.Basis.repr_self, Finsupp.single_apply]
  ring

theorem norm_gEmb (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  rw [← Algebra.norm_norm (S := F), norm_gEmb_F]
  have h := prod_emb (F := F) (a ^ 2 + b ^ 2)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← h, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp

end GlobalTheory.GaussExt
end
end

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (a b : F), ((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  atlas_forward_decl GlobalTheory.GaussExt.norm_gEmb
end

section
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussExt.UnitIdx

variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]

theorem aeval_neg_ii : aeval (-ii F) (X ^ 2 + 1 : F[X]) = 0 := by
  simp only [map_add, map_pow, aeval_X, map_one, neg_sq, ii_sq F]; ring

def conj : Ext F →ₐ[F] Ext F := AdjoinRoot.liftAlgHom (X ^ 2 + 1 : F[X]) (Algebra.ofId F (Ext F)) (-ii F)
  (by have := aeval_neg_ii F; rwa [aeval_def] at this)

theorem conj_ii : conj F (ii F) = -ii F := by
  simp [conj, ii]

theorem conj_algebraMap (a : F) : conj F (algebraMap F (Ext F) a) = algebraMap F (Ext F) a :=
  (conj F).commutes a

theorem exists_repr (x : Ext F) : ∃ a b : F, x = algebraMap F (Ext F) a + algebraMap F (Ext F) b * ii F := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hm : (X ^ 2 + 1 : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  set r := p %ₘ (X ^ 2 + 1 : F[X])
  have hr : AdjoinRoot.mk (X ^ 2 + 1 : F[X]) p = AdjoinRoot.mk _ r := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 + 1), by have := modByMonic_add_div p (X ^ 2 + 1 : F[X]); linear_combination -this⟩
  have hrd : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p hm (by intro h; have := congrArg natDegree h; rw [hdeg] at this; simp at this)
    change (p %ₘ (X ^ 2 + 1 : F[X])).natDegree ≤ 1
    omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hr, eq_X_add_C_of_natDegree_le_one hrd]
  simp [ii, AdjoinRoot.algebraMap_eq, add_comm]

theorem ii_ne_zero : ii F ≠ 0 := by
  intro h
  have := ii_sq F
  rw [h] at this
  norm_num at this

theorem mem_range_of_conj_eq (x : Ext F) (hx : conj F x = x) : ∃ a : F, algebraMap F (Ext F) a = x := by
  obtain ⟨a, b, rfl⟩ := exists_repr F x
  refine ⟨a, ?_⟩
  simp only [map_add, map_mul, conj_algebraMap, conj_ii] at hx
  have h2 : (2 : Ext F) * algebraMap F (Ext F) b * ii F = 0 := by linear_combination -hx
  have hb : algebraMap F (Ext F) b = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h two_ne_zero
      · exact h
    · exact absurd h (ii_ne_zero F)
  rw [hb]; ring

theorem embedding_conj (φ : Ext F →+* ℂ) (x : Ext F) : φ (conj F x) = starRingEnd ℂ (φ x) := by
  have key : φ.comp (conj F).toRingHom = (starRingEnd ℂ).comp φ := by
    apply AdjoinRoot.ringHom_ext
    · ext a
      have hre := NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F (Ext F)))
      have h1 := hre.coe_embedding_apply a
      simp only [RingHom.comp_apply, AdjoinRoot.algebraMap_eq] at h1 ⊢
      have h3 : (conj F).toRingHom (AdjoinRoot.of _ a) = AdjoinRoot.of _ a := by
        rw [← AdjoinRoot.algebraMap_eq]; exact conj_algebraMap F a
      rw [h3, ← h1, Complex.conj_ofReal]
    · have h := congrArg φ (ii_sq F)
      simp only [map_pow, map_neg, map_one] at h
      have hc : (φ (ii F) - I) * (φ (ii F) + I) = 0 := by linear_combination h - I_sq
      simp only [RingHom.comp_apply]
      change φ (conj F (ii F)) = starRingEnd ℂ (φ (ii F))
      rw [conj_ii, map_neg]
      rcases mul_eq_zero.1 hc with h' | h'
      · rw [sub_eq_zero.1 h']; simp
      · rw [eq_neg_of_add_eq_zero_left h']; simp
  exact congrArg (fun f => f x) key

theorem isIntegral_conj {x : Ext F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F x) :=
  hx.map ((conj F).toRingHom.toIntAlgHom)

theorem pow_mem_range (u : (𝓞 (Ext F))ˣ) :
    ∃ m : ℕ, 0 < m ∧ u ^ m ∈ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range := by
  set x : Ext F := ((u : 𝓞 (Ext F)) : Ext F)
  set y : Ext F := (((u⁻¹ : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) : Ext F)
  have hxy : x * y = 1 := by
    have := congrArg (fun z : 𝓞 (Ext F) => (z : Ext F)) u.mul_inv
    simpa [x, y] using this
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hint : IsIntegral ℤ (x * conj F y) :=
    (RingOfIntegers.isIntegral_coe _).mul (isIntegral_conj F (RingOfIntegers.isIntegral_coe _))
  obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (Ext F) ℂ hint fun φ => by
    have h1 : φ x * φ y = 1 := by rw [← map_mul, hxy, map_one]
    rw [map_mul, embedding_conj, norm_mul, Complex.norm_conj, ← norm_mul, h1, norm_one]
  refine ⟨m, hm, ?_⟩

  have hcxy : conj F x * conj F y = 1 := by rw [← map_mul, hxy, map_one]
  have hfix : conj F (x ^ m) = x ^ m := by
    have : (x * conj F y) ^ m * (conj F x) ^ m = (conj F x) ^ m := by rw [hpow, one_mul]
    rw [map_pow, ← this, ← mul_pow, mul_assoc, mul_comm (conj F y), hcxy, mul_one]
  obtain ⟨a, ha⟩ := mem_range_of_conj_eq F _ hfix
  have hai : IsIntegral ℤ a := by
    refine (isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_
    rw [ha]; exact (RingOfIntegers.isIntegral_coe _).pow m

  have hfix' : conj F (y ^ m) = y ^ m := by
    have e : y ^ m = (x ^ m)⁻¹ := by rw [← inv_pow, inv_eq_of_mul_eq_one_right hxy]
    rw [e, map_inv₀, hfix]
  obtain ⟨b, hb⟩ := mem_range_of_conj_eq F _ hfix'
  have hbi : IsIntegral ℤ b := by
    refine (isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_
    rw [hb]; exact (RingOfIntegers.isIntegral_coe _).pow m
  have hab : a * b = 1 := by
    apply (algebraMap F (Ext F)).injective
    rw [map_mul, ha, hb, ← mul_pow, hxy, one_pow, map_one]
  let A : 𝓞 F := ⟨a, hai⟩
  let B : 𝓞 F := ⟨b, hbi⟩
  have hAB : A * B = 1 := RingOfIntegers.ext hab
  refine ⟨⟨A, B, hAB, by rw [mul_comm]; exact hAB⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  rw [show (((u : 𝓞 (Ext F)) ^ m : 𝓞 (Ext F)) : Ext F) = x ^ m by simp [x], ← ha]
  rfl

theorem finite_quot : Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
    (Units.map (algebraMap (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  haveI : Group.FG (𝓞 (Ext F))ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  refine CommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hu⟩ := pow_mem_range F u
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hu

end GlobalTheory.GaussExt.UnitIdx

theorem GlobalTheory.GaussExt.finite_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
      (Units.map (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) :=
  fun F _ _ _ => GlobalTheory.GaussExt.UnitIdx.finite_quot F
end
end

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_gaussianExtension_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  atlas_forward_decl GlobalTheory.GaussExt.finite_units_quot_units
end

section
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussSum

open GlobalTheory.GaussExt

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem eq_zero_of_add_mul_ii {x y : F}
    (h : algebraMap F (Ext F) x + algebraMap F (Ext F) y * ii F = 0) : x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy
    have hy' : algebraMap F (Ext F) y ≠ 0 := (_root_.map_ne_zero _).2 hy
    have hi : ii F = algebraMap F (Ext F) (-x / y) := by
      rw [map_div₀, map_neg, eq_div_iff hy']
      linear_combination h
    have h2 : algebraMap F (Ext F) ((-x / y) ^ 2 + 1) = 0 := by
      rw [map_add, map_pow, ← hi, ii_sq, map_one]; ring
    have h3 : (-x / y) ^ 2 + 1 = 0 := (map_eq_zero _).1 h2
    obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
      obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
      exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
    have h4 := congrArg τ h3
    rw [map_add, map_pow, map_one, map_zero] at h4
    nlinarith [sq_nonneg (τ (-x / y))]
  refine ⟨?_, hy⟩
  rw [hy, map_zero, zero_mul, add_zero] at h
  exact (map_eq_zero _).1 h

theorem isIntegral_ii : IsIntegral ℤ (ii F) :=
  ⟨X ^ 2 + 1, by monicity!, by simp [ii_sq]⟩

set_option maxHeartbeats 1000000 in

theorem summable_norm_rpow (𝔞 𝔟 : Frac F) {t : ℝ} (ht : 1 < t)
    (hQ : Finite ((𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range)) :
    Summable (fun c : Quotient (latRel 𝔞 𝔟) => |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := APart.exists_den (latM 𝔞)
  obtain ⟨d₂, hd₂, h₂⟩ := APart.exists_den (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  have hd : ((d₁ : F) * (d₂ : F)) ≠ 0 := mul_ne_zero (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)
  choose ga hga using fun c : Quotient (latRel 𝔞 𝔟) => h₁ c.out.1.1 c.out.2.1
  choose gb hgb using fun c : Quotient (latRel 𝔞 𝔟) => h₂ c.out.1.2 c.out.2.2.1
  let iO : 𝓞 (Ext F) := ⟨ii F, isIntegral_ii⟩
  let y : Quotient (latRel 𝔞 𝔟) → 𝓞 (Ext F) := fun c =>
    algebraMap (𝓞 F) (𝓞 (Ext F)) (d₂ * ga c) + algebraMap (𝓞 F) (𝓞 (Ext F)) (d₁ * gb c) * iO
  have hy : ∀ c, ((y c : 𝓞 (Ext F)) : Ext F) = algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) * gEmb F c.out.1 := by
    intro c
    have e : ((y c : 𝓞 (Ext F)) : Ext F) =
        algebraMap F (Ext F) ((d₂ * ga c : 𝓞 F) : F) + algebraMap F (Ext F) ((d₁ * gb c : 𝓞 F) : F) * ii F := rfl
    have ea : ((d₂ * ga c : 𝓞 F) : F) = (d₂ : F) * (ga c : F) := rfl
    have eb : ((d₁ * gb c : 𝓞 F) : F) = (d₁ : F) * (gb c : F) := rfl
    rw [e, ea, eb, hga, hgb, gEmb]
    simp only [map_mul]
    ring

  let rep : Ideal (𝓞 (Ext F)) → 𝓞 (Ext F) := fun J =>
    if h : ∃ x, J = Ideal.span {x} then h.choose else 0
  have hrep : ∀ c, Associated (rep (Ideal.span {y c})) (y c) := by
    intro c
    have hex : ∃ x, Ideal.span {y c} = Ideal.span {x} := ⟨y c, rfl⟩
    refine Ideal.span_singleton_eq_span_singleton.1 ?_
    simp only [rep, dif_pos hex]
    exact hex.choose_spec.symm
  choose u hu using hrep
  let Q := (𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range
  let φ : Quotient (latRel 𝔞 𝔟) → Ideal (𝓞 (Ext F)) × Q := fun c =>
    (Ideal.span {y c}, (QuotientGroup.mk (u c) : Q))
  have hinj : Function.Injective φ := by
    intro c c' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hJ, hq⟩ := h
    obtain ⟨η, hη⟩ := QuotientGroup.eq.1 hq
    have hu' : ((u c' : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) = (u c : 𝓞 (Ext F)) * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      have : u c' = u c * Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom η := by
        rw [hη]; group
      rw [this]; simp
    have key : y c' = y c * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      rw [← hu c', ← hu c, ← hJ, hu']; ring
    have h3 : ((y c' : 𝓞 (Ext F)) : Ext F) = (y c : Ext F) * algebraMap F (Ext F) ((η : 𝓞 F) : F) := by
      rw [key]; rfl
    rw [hy, hy] at h3
    have h4 : gEmb F c'.out.1 = gEmb F c.out.1 * algebraMap F (Ext F) ((η : 𝓞 F) : F) :=
      mul_left_cancel₀ ((_root_.map_ne_zero _).2 hd) (by rw [h3]; ring)
    unfold gEmb at h4
    have h5 : algebraMap F (Ext F) (c'.out.1.1 - ((η : 𝓞 F) : F) * c.out.1.1) +
        algebraMap F (Ext F) (c'.out.1.2 - ((η : 𝓞 F) : F) * c.out.1.2) * ii F = 0 := by
      simp only [map_sub, map_mul]
      linear_combination h4
    obtain ⟨e1, e2⟩ := eq_zero_of_add_mul_ii h5
    exact (Quotient.out_equiv_out.1 ⟨η, by linear_combination e1, by linear_combination e2⟩)
  haveI := hQ
  have hS : Summable (fun p : Ideal (𝓞 (Ext F)) × Q => ((Ideal.absNorm p.1 : ℕ) : ℝ) ^ (-t) * (fun _ : Q => (1 : ℝ)) p.2) :=
    (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal (Ext F) ht).mul_of_nonneg (Summable.of_finite)
      (fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ => zero_le_one)
  have hS' := hS.comp_injective hinj
  set K : ℝ := |((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ)| with hK
  have hK0 : 0 < K := by
    rw [hK]
    have h0 : algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) ≠ 0 := (_root_.map_ne_zero _).2 hd
    have h1 : Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) ≠ 0 := Algebra.norm_ne_zero_iff.2 h0
    exact abs_pos.2 (by exact_mod_cast h1)
  refine (hS'.mul_left (K ^ t)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (y c) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) * Algebra.norm ℚ (gEmb F c.out.1) := by
    rw [Algebra.coe_norm_int, hy, map_mul]
  have e2 : ((Algebra.norm ℤ (y c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ) * ((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({y c} : Set (𝓞 (Ext F)))) : ℕ) : ℝ) =
      K * |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply, φ, mul_one]
  rw [hN, Real.mul_rpow hK0.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hK0, add_neg_cancel,
    Real.rpow_zero, one_mul]

end GlobalTheory.GaussSum

theorem GlobalTheory.GaussSum.summable_gauss_norm : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  intro F _ _ _ 𝔞 𝔟 t ht hQ
  exact GlobalTheory.GaussSum.summable_norm_rpow 𝔞 𝔟 ht hQ
end
end

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_gaussianExtension_norm_rpow : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  atlas_forward_decl GlobalTheory.GaussSum.summable_gauss_norm
end

section
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound

theorem normSq_lower (w : ℂ) (a b : ℝ) :
    (w.im) ^ 2 / (1 + ‖w‖ ^ 2) * (a ^ 2 + b ^ 2) ≤ ‖(a : ℂ) + b * w‖ ^ 2 := by
  have h1 : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h1]
  have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn : ‖(a : ℂ) + b * w‖ ^ 2 = (a + b * w.re) ^ 2 + (b * w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hw, hn]
  nlinarith [sq_nonneg (a + b * w.re), sq_nonneg ((a + b * w.re) * w.re + b * w.im * w.im)]

theorem bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  intro F _ _ σ hσ z hz
  set s := σ.re with hs
  let c : (F →+* ℝ) → ℝ := fun τ => 4 * Real.pi ^ 2 * ((z τ).im ^ 2 / (1 + ‖z τ‖ ^ 2))
  have hc : ∀ τ, 0 < c τ := fun τ => by have := hz τ; positivity
  refine ⟨(∏ τ, c τ) ^ (-(1 + s)), fun p hp => ?_⟩
  set P := ∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2) with hPdef
  have hP : 0 < P := Finset.prod_pos fun τ _ => by
    by_contra h
    push_neg at h
    have h1 : τ p.1 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    have h2 : τ p.2 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    exact hp (Prod.ext ((map_eq_zero τ).1 h1) ((map_eq_zero τ).1 h2))
  set N := ∏ τ, ‖latPt z p τ‖ with hN
  have hNpos : 0 < N := Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz hp τ)
  have hterm : ‖eisTerm 2 σ z p‖ = (N ^ 2) ^ (-(1 + s)) := by
    unfold eisTerm
    simp only [norm_mul, norm_pow, norm_inv, norm_prod]
    rw [← hN, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) from (Real.rpow_two N).symm, ← Real.rpow_mul hNpos.le]
    have : (2 : ℝ) * (-(1 + s)) = -(2 : ℝ) + (-2 * σ).re := by simp [hs]; ring
    rw [this, Real.rpow_add hNpos, Real.rpow_neg hNpos.le, Real.rpow_two, inv_pow]
  have hlow : (∏ τ, c τ) * P ≤ N ^ 2 := by
    rw [hPdef, hN, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun τ _ => mul_nonneg (hc τ).le (by positivity)) fun τ _ => ?_
    have hl : ‖latPt z p τ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖((τ p.1 : ℝ) : ℂ) + (τ p.2 : ℝ) * z τ‖ ^ 2 := by
      simp only [latPt, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hl, mul_assoc (4 * Real.pi ^ 2)]
    exact mul_le_mul_of_nonneg_left (normSq_lower (z τ) _ _) (by positivity)
  rw [hterm, ← Real.mul_rpow (Finset.prod_nonneg fun τ _ => (hc τ).le) hP.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (Finset.prod_pos fun τ _ => hc τ) hP) hlow (by linarith)

end GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
end

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  atlas_forward_decl GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound
end

section
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.summable_eisClass_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  intro F _ _ _ 𝔞 𝔟 σ hσ z hz
  obtain ⟨C, hC⟩ := GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound F σ hσ z hz
  have hS := (GlobalTheory.T.summable_gaussianExtension_norm_rpow F 𝔞 𝔟 (1 + σ.re) (by linarith) (GlobalTheory.T.finite_gaussianExtension_units_quot_units F)).mul_left C
  refine Summable.of_norm_bounded hS fun c => ?_
  have hp : c.out.1 ≠ 0 := c.out.2.2.2
  have e : |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| =
      ∏ τ : F →+* ℝ, ((τ c.out.1.1) ^ 2 + (τ c.out.1.2) ^ 2) := by
    rw [GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair F c.out.1.1 c.out.1.2]
    exact abs_of_nonneg (Finset.prod_nonneg fun τ _ => by positivity)
  rw [e]
  exact hC _ hp
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.summable_eisClass_two
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.Regroup

variable {F : Type} [Field F] [NumberField F]

theorem unit_mul_mem {I : FractionalIdeal (𝓞 F)⁰ F} (ε : (𝓞 F)ˣ) {a : F} (ha : a ∈ I) :
    ((ε : 𝓞 F) : F) * a ∈ I := by
  have : (ε : 𝓞 F) • a ∈ (I : Submodule (𝓞 F) F) := Submodule.smul_mem _ _ ha
  rwa [Algebra.smul_def] at this

theorem unit_eq_one {ε : (𝓞 F)ˣ} {b : F} (hb : b ≠ 0) (h : ((ε : 𝓞 F) : F) * b = b) : ε = 1 := by
  have h1 : ((ε : 𝓞 F) : F) = 1 := mul_right_cancel₀ hb (h.trans (one_mul b).symm)
  apply Units.ext
  apply RingOfIntegers.ext
  simpa using h1

variable (𝔞 𝔟 : Frac F)

theorem mk_eq {p q : LatPair 𝔞 𝔟} (ε : (𝓞 F)ˣ) (h1 : q.1.1 = ((ε : 𝓞 F) : F) * p.1.1)
    (h2 : q.1.2 = ((ε : 𝓞 F) : F) * p.1.2) : Quotient.mk (latRel 𝔞 𝔟) p = Quotient.mk _ q :=
  Quotient.sound (Exists.intro ε ⟨h1, h2⟩)

theorem mkU_eq {I : FractionalIdeal (𝓞 F)⁰ F} {x y : NZ I} (ε : (𝓞 F)ˣ) (h : y.1 = ((ε : 𝓞 F) : F) * x.1) :
    Quotient.mk (unitRel I) x = Quotient.mk _ y :=
  Quotient.sound (Exists.intro ε h)

def leftPt (c : Quotient (unitRel (latM 𝔞))) : LatPair 𝔞 𝔟 :=
  ⟨(c.out.1, 0), c.out.2.1, ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F).zero_mem, fun h => c.out.2.2 (congrArg Prod.fst h)⟩

def rightPt (c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) (a : {a : F // a ∈ latM 𝔞}) : LatPair 𝔞 𝔟 :=
  ⟨(a.1, c.out.1), a.2, c.out.2.1, fun h => c.out.2.2 (congrArg Prod.snd h)⟩

def regroupMap : Quotient (unitRel (latM 𝔞)) ⊕
    (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), {a : F // a ∈ latM 𝔞}) → Quotient (latRel 𝔞 𝔟)
  | Sum.inl c => Quotient.mk _ (leftPt 𝔞 𝔟 c)
  | Sum.inr s => Quotient.mk _ (rightPt 𝔞 𝔟 s.1 s.2)

theorem regroupMap_injective : Function.Injective (regroupMap 𝔞 𝔟) := by
  rintro (c | ⟨c, a⟩) (c' | ⟨c', a'⟩) h
  · obtain ⟨ε, h1, -⟩ := Quotient.exact h
    congr 1
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact mkU_eq ε h1
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    exact absurd (h2.trans (mul_zero _)) c'.out.2.2
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    dsimp only [leftPt, rightPt] at h2
    have := congrArg (fun x => (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * x) h2
    simp only [← mul_assoc, unit_inv_mul, one_mul, mul_zero] at this
    exact absurd this.symm c.out.2.2
  · obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact mkU_eq ε h2
    subst hc
    have hε : ε = 1 := unit_eq_one c.out.2.2 h2.symm
    subst hε
    have ha : a' = a := Subtype.ext (by simpa [rightPt] using h1)
    subst ha
    rfl

theorem regroupMap_surjective : Function.Surjective (regroupMap 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
  obtain ⟨⟨a, b⟩, ha, hb, hne⟩ := p
  by_cases hb0 : b = 0
  · subst hb0
    have ha0 : a ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ε, hε⟩ : (unitRel (latM 𝔞)).r ⟨a, ha, ha0⟩ (Quotient.mk (unitRel (latM 𝔞)) ⟨a, ha, ha0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inl (Quotient.mk _ ⟨a, ha, ha0⟩), (mk_eq 𝔞 𝔟 ε hε (mul_zero _).symm).symm⟩
  · obtain ⟨ε, hε⟩ : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r ⟨b, hb, hb0⟩
        (Quotient.mk (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ⟨b, hb, hb0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inr ⟨Quotient.mk _ ⟨b, hb, hb0⟩, ⟨_, unit_mul_mem ε ha⟩⟩, (mk_eq 𝔞 𝔟 ε rfl hε).symm⟩

theorem g_out {g : F × F → ℂ}
    (hg : ∀ (ε : (𝓞 F)ˣ) (a b : F), g (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = g (a, b))
    (p : LatPair 𝔞 𝔟) : g (Quotient.mk (latRel 𝔞 𝔟) p).out.1 = g p.1 := by
  obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
  have : p.1 = (((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1,
      ((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2) := Prod.ext h1 h2
  rw [this, hg]

end GlobalTheory.HeckeTwo.Regroup

theorem GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  intro F _ _ 𝔞 𝔟 g hg hs
  open GlobalTheory.HeckeTwo.Regroup in
  let e := Equiv.ofBijective _ ⟨regroupMap_injective 𝔞 𝔟, regroupMap_surjective 𝔞 𝔟⟩
  let h : Quotient (unitRel (latM 𝔞)) ⊕
      (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), {a : F // a ∈ latM 𝔞}) → ℂ :=
    Sum.elim (fun c => g (c.out.1, 0)) (fun s => g (s.2.1, s.1.out.1))
  have hfe : (fun c : Quotient (latRel 𝔞 𝔟) => g c.out.1) ∘ e = h := by
    funext x
    rcases x with c | ⟨c, a⟩
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
  have hsh : Summable h := hfe ▸ (e.summable_iff).2 hs
  have hl : Summable (h ∘ Sum.inl) := hsh.comp_injective Sum.inl_injective
  have hr : Summable (h ∘ Sum.inr) := hsh.comp_injective Sum.inr_injective
  have hr' : Summable (fun s : (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)),
      {a : F // a ∈ latM 𝔞}) => g (s.2.1, s.1.out.1)) := hr
  refine ⟨hl, fun c => hr'.sigma_factor c, hr'.sigma, ?_⟩
  rw [← e.tsum_eq, show (∑' x, g (e x).out.1) = ∑' x, h x from congrArg tsum hfe, hl.tsum_sum hr]
  exact congrArg₂ (· + ·) rfl hr'.tsum_sigma
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_latticePair_unitQuotient_regroup : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem phi_ofReal_mul (σ : ℂ) (y : ℝ) (w : ℂ) :
    phi σ ((y : ℂ) * w) = (((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg y) (norm_nonneg w)]
  have h : ((y : ℂ))⁻¹ ^ 2 = ((|y| : ℝ) : ℂ)⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, ← ofReal_pow, ← ofReal_pow, sq_abs]
  rw [mul_inv, mul_pow, h]
  ring

theorem hTrans_zero_eq (σ : ℂ) (y : ℝ) (hy : y ≠ 0) :
    hTrans σ 0 y = cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  have h0 : hTrans σ 0 y = ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) := by simp [hTrans]
  have h1 : cConst σ = ∫ t : ℝ, phi σ ((t : ℂ) + I) := by simp [cConst, hTrans]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) y
  have h2 : (∫ u : ℝ, phi σ (((y * u : ℝ) : ℂ) + (y : ℂ) * I)) =
      (((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) * ∫ u : ℝ, phi σ ((u : ℂ) + I) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext u
    rw [← phi_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [h2] at hsub
  have hya : (|y| : ℝ) ≠ 0 := abs_ne_zero.mpr hy
  have hyc : ((|y| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hya
  have h3 : (∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I)) =
      ((|y| : ℝ) : ℂ) * ((((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) *
        ∫ u : ℝ, phi σ ((u : ℂ) + I)) := by
    rw [hsub, abs_inv, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hyc, one_mul]
  have hc : ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) = ((|y| : ℝ) : ℂ)⁻¹ * ((|y| : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [show (-1 - 2 * σ) = -1 + -2 * σ by ring, cpow_add _ _ hyc, cpow_neg_one]
  rw [h0, h3, ← h1, hc]
  field_simp

end GlobalTheory.HeckeTwo
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_zero_eq : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.hTrans_zero_eq
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.PartialZetaSum

variable {F : Type} [Field F] [NumberField F]

theorem exists_ideal (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ J : Ideal (𝓞 F), (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [← FractionalIdeal.le_one_iff_exists_coeIdeal]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
      ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 b.2.1) _
    _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

def idealOf (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : Ideal (𝓞 F) := (exists_ideal 𝔟 b).choose

theorem idealOf_coe (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
  (exists_ideal 𝔟 b).choose_spec

theorem span_eq (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [idealOf_coe, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem idealOf_mem (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : idealOf 𝔟 b ∈ (Ideal (𝓞 F))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have h1 := span_eq 𝔟 b
  rw [h] at h1
  simp at h1
  exact b.2.2 (FractionalIdeal.spanSingleton_eq_zero_iff.1 h1)

theorem idealOf_class (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ = (ClassGroup.mk F 𝔟)⁻¹ := by
  rw [← ClassGroup.mk_mk0 F, ← map_inv]
  have hb : (b.1 : F) ≠ 0 := b.2.2
  have h : FractionalIdeal.mk0 F ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ =
      toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb) * 𝔟⁻¹ := by
    apply Units.ext
    rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, idealOf_coe]
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb)) = 1 := by
    rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  rw [h, map_mul, hp, one_mul]

theorem rel_of_idealOf_eq (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : idealOf 𝔟 b = idealOf 𝔟 b') : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b' := by
  have h2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b'.1 := by
    rw [span_eq, span_eq, h]
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h2
  exact ⟨z, by rw [← hz, Units.smul_def, Algebra.smul_def]⟩

theorem idealOf_eq_of_rel (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b') : idealOf 𝔟 b = idealOf 𝔟 b' := by
  obtain ⟨ε, hε⟩ := h
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe, idealOf_coe, hε]
  congr 1
  exact FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, by rw [Units.smul_def, Algebra.smul_def]⟩

theorem exists_of_class (𝔟 : Frac F) (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹) :
    ∃ b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F), idealOf 𝔟 b = J.1 := by
  have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * 𝔟) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hJ, inv_mul_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hx' : ((FractionalIdeal.mk0 F J * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    beta_reduce
    rw [FractionalIdeal.coe_spanSingleton]; exact hx
  rw [Units.val_mul, FractionalIdeal.coe_mk0] at hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx'
    exact (mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero J)) (Units.ne_zero 𝔟)) hx'
  have hxm : x ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
    have : FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [← hx']
      calc ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
          ≤ 1 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
        _ = _ := one_mul _
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 this
  let b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := ⟨x, hxm, hx0⟩
  refine ⟨b, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe]
  show FractionalIdeal.spanSingleton (𝓞 F)⁰ x * _ = _
  rw [← hx', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem norm_eq (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    |((Algebra.norm ℚ b.1 : ℚ) : ℝ)| = (Ideal.absNorm (idealOf 𝔟 b) : ℝ) * nrm 𝔟 := by
  have h2 := congrArg FractionalIdeal.absNorm (span_eq 𝔟 b)
  rw [FractionalIdeal.absNorm_span_singleton, map_mul, FractionalIdeal.coeIdeal_absNorm] at h2
  unfold nrm
  rw [← Rat.cast_abs, h2]; push_cast; ring

theorem nrm_nonneg (𝔟 : Frac F) : 0 ≤ nrm 𝔟 := by
  unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _

theorem hasSum_norm_cpow : ∀ (F : Type) [Field F] [NumberField F] (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ s : ℂ, 1 < s.re → HasSum (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-s)) (((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔟 : ℝ) : ℂ) ^ (-s) * Zb s) := by
  intro F _ _ 𝔟 Zb hZ s hs
  let e : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) →
      {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹} :=
    fun c => ⟨⟨idealOf 𝔟 c.out, idealOf_mem 𝔟 c.out⟩, idealOf_class 𝔟 c.out⟩
  have he : Function.Bijective e := by
    constructor
    · intro c c' h
      have h' : idealOf 𝔟 c.out = idealOf 𝔟 c'.out := congrArg (fun J => (J.1.1 : Ideal (𝓞 F))) h
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact Quotient.sound (rel_of_idealOf_eq 𝔟 h')
    · intro J
      obtain ⟨b, hb⟩ := exists_of_class 𝔟 J.1 J.2
      refine ⟨Quotient.mk _ b, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show idealOf 𝔟 (Quotient.mk _ b).out = J.1.1
      rw [← hb]; exact idealOf_eq_of_rel 𝔟 (Quotient.exact (Quotient.out_eq _))
  have key := (hZ.2 s hs).mul_left (((nrm 𝔟 : ℝ) : ℂ) ^ (-s))
  rw [← (Equiv.ofBijective e he).hasSum_iff] at key
  refine (congrArg (fun f => HasSum f _) ?_).mpr key
  funext c
  simp only [Function.comp_apply, Equiv.ofBijective_apply, e]
  rw [norm_eq 𝔟 c.out, ofReal_mul, mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (nrm_nonneg 𝔟), mul_comm,
    ofReal_natCast]

end GlobalTheory.PartialZetaSum
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_abs_norm_cpow_unitClasses_partialZeta : ∀ (F : Type) [Field F] [NumberField F] (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ s : ℂ, 1 < s.re → HasSum (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-s)) (((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔟 : ℝ) : ℂ) ^ (-s) * Zb s) := by
  atlas_forward_decl GlobalTheory.PartialZetaSum.hasSum_norm_cpow
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoEq

theorem ofReal_prod_cpow {ι : Type} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (c : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ c = ∏ i ∈ s, ((r i : ℂ) ^ c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr j (Finset.mem_insert_self _ _)) (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

variable {F : Type} [Field F] [NumberField F]

theorem eisTerm_eq_kFac (σ : ℂ) (z : Emb F → ℂ) (a b : F) :
    eisTerm 2 σ z (a, b) = kFac F σ * ∏ τ : Emb F, phi σ ((τ a : ℂ) + (τ b : ℂ) * z τ) := by
  unfold eisTerm kFac phi
  rw [← Finset.prod_mul_distrib, norm_prod, ofReal_prod_cpow _ _ (fun _ _ => norm_nonneg _), ← Finset.prod_inv_distrib,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hn : ‖latPt z (a, b) τ‖ = (2 * Real.pi) * ‖(τ a : ℂ) + (τ b : ℂ) * z τ‖ := by
    simp only [latPt, norm_mul, norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  simp only [latPt, mul_inv, mul_pow]
  ring

theorem split_zero (I : FractionalIdeal (𝓞 F)⁰ F) (g : F → ℂ) (h : Summable (fun ν : {ν : F // ν ∈ I} => g ν.1)) :
    ∑' ν : {ν : F // ν ∈ I}, g ν.1 = g 0 + ∑' ν : NZ I, g ν.1 := by
  classical
  have h0 : (0 : F) ∈ I := (I : Submodule (𝓞 F) F).zero_mem
  rw [h.tsum_eq_add_tsum_ite ⟨0, h0⟩]
  congr 1
  let e : NZ I → {ν : F // ν ∈ I} := fun ν => ⟨ν.1, ν.2.1⟩
  have he : Function.Injective e := fun x y hxy => Subtype.ext (congrArg Subtype.val hxy : _)
  rw [← he.tsum_eq]
  · refine tsum_congr fun ν => ?_
    have : e ν ≠ ⟨0, h0⟩ := fun h' => ν.2.2 (congrArg Subtype.val h' : _)
    simp only [this, if_false, e]
  · intro x hx
    have hx0 : x ≠ ⟨0, h0⟩ := by
      intro h'; apply hx; simp [h']
    exact ⟨⟨x.1, x.2, fun h' => hx0 (Subtype.ext h')⟩, rfl⟩

theorem prod_abs_emb [IsTotallyReal F] (b : F) : ∏ τ : Emb F, |τ b| = |((Algebra.norm ℚ b : ℚ) : ℝ)| := by
  rw [← Finset.abs_prod]
  congr 1
  apply Complex.ofReal_injective
  push_cast
  exact prod_emb b

theorem fTerm_zero [IsTotallyReal F] (hzero : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ)) (σ : ℂ) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b : F} (hb : b ≠ 0) :
    fTerm σ z b 0 = (∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))) *
      ((|((Algebra.norm ℚ b : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  unfold fTerm
  rw [← prod_abs_emb, ofReal_prod_cpow _ _ (fun _ _ => abs_nonneg _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hy : 0 < (z τ).im := hz τ
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  rw [map_zero, zero_mul, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    hzero σ _ (mul_ne_zero hτb hy.ne'), abs_mul, abs_of_pos hy, ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg _) hy.le]
  ring

theorem gFun_eq_eisSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  intro F _ _ _ 𝔞 𝔟 Zb hZ σ hσ z hz
  have hS := GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two F 𝔞 𝔟 σ hσ z hz
  refine ⟨hS, ?_⟩
  have hinv : ∀ (ε : (𝓞 F)ˣ) (a b : F),
      eisTerm 2 σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = eisTerm 2 σ z (a, b) :=
    fun ε a b => eisTerm_unit even_two σ z ε a b
  obtain ⟨-, -, hBs, hsum⟩ := GlobalTheory.T.tsum_latticePair_unitQuotient_regroup F 𝔞 𝔟 (eisTerm 2 σ z) hinv hS
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  set P : ℂ := ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) with hPdef
  set K : ℂ := kFac F σ * (omegaFactor 𝔞 : ℂ) with hKdef
  have hper : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' a : {a : F // a ∈ latM 𝔞}, eisTerm 2 σ z (a.1, c.out.1) =
        K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1 := by
    intro c
    have hb : c.out.1 ≠ 0 := c.out.2.2
    obtain ⟨hfs, hP⟩ := GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal F 𝔞 σ hσ z hz c.out.1 hb
    simp_rw [eisTerm_eq_kFac]
    rw [tsum_mul_left, hP.tsum_eq, split_zero _ _ hfs, fTerm_zero GlobalTheory.T.heckePhiFourierTransform_zero_eq σ hz hb]
    ring
  have hz2 := GlobalTheory.T.hasSum_abs_norm_cpow_unitClasses_partialZeta F 𝔟 Zb hZ (1 + 2 * σ) (by simp; linarith)
  rw [show -(1 + 2 * σ) = -1 - 2 * σ by ring] at hz2
  have hX := hz2.mul_left (K * P)
  have hT : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) := by
    simpa only [hper] using hBs
  have hY : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) :=
    (hT.sub hX.summable).congr fun c => by ring
  unfold eisSum eisClass
  rw [hsum, tsum_congr hper, hX.summable.tsum_add hY, hX.tsum_eq, tsum_mul_left]
  have hA : ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ z (c.out.1, 0) = aPart 𝔞 σ :=
    tsum_congr fun c => by simp [eisTerm, latPt]
  rw [hA]
  unfold gFun bZero bOne
  rw [if_neg hσ0]
  ring

end GlobalTheory.HeckeTwoEq
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwoContinuation_eq_latticeSeries : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  atlas_forward_decl GlobalTheory.HeckeTwoEq.gFun_eq_eisSum
end
