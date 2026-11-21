import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpProps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominators
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlaneProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHom

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

def constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) : Ω →+* ring ε.range where
  toFun c := ⟨fun _ => ε c, mem_ring_of_inR ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).2 _ ⟨c, rfl⟩)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def evAt (E : Subring ℂ) (τ : ℍ) : ring E →+* ℂ := (Pi.evalRingHom (fun _ : ℍ => ℂ) τ).comp (ring E).subtype

theorem evAt_apply (E : Subring ℂ) (τ : ℍ) (x : ring E) : evAt E τ x = (x : ℍ → ℂ) τ := rfl

theorem evAt_comp_constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (τ : ℍ) :
    (evAt ε.range τ).comp (constHom ε) = ε := by
  ext c; rfl

theorem io_comp_constHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) :
    T.io.comp (constHom ε) = algebraMap Ω T.K := by
  ext c; exact T.io_c c _ rfl

theorem isIntegral_io_adjoin_j (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : ring ε.range) (ha : (a : ℍ → ℂ) = jT) (b : ring ε.range) :
    IsIntegral (IntermediateField.adjoin Ω {T.io a}) (T.io b) := by
  set L := IntermediateField.adjoin Ω {T.io a}
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range b (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2)
  have hl : ∀ i, c i ∈ Polynomial.lifts ε := fun i =>
    (Polynomial.lifts_iff_coeff_lifts _).2 fun k => RingHom.mem_range.1 (hc i k)
  choose d hd using fun i => (Polynomial.mem_lifts (c i)).1 (hl i)
  let xa : L := ⟨T.io a, IntermediateField.mem_adjoin_simple_self Ω _⟩
  let φ : Polynomial Ω →ₐ[Ω] L := Polynomial.aeval xa

  have hr : b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ) = 0 := by
    apply Subtype.ext; funext τ
    have h := hrel τ
    have key : evAt ε.range τ (b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ)) = 0 := by
      simp only [map_add, map_sum, map_mul, map_pow, Polynomial.hom_eval₂, evAt_comp_constHom,
        evAt_apply, ha]
      simpa [← Polynomial.eval_map, hd] using h
    simpa [evAt_apply] using key
  have hK : T.io b ^ n + ∑ i, Polynomial.aeval (T.io a) (d i) * T.io b ^ (i : ℕ) = 0 := by
    have := congrArg T.io hr
    simp only [map_add, map_sum, map_mul, map_pow, Polynomial.hom_eval₂, io_comp_constHom, map_zero] at this
    simpa [Polynomial.aeval_def] using this
  refine ⟨Polynomial.X ^ n + ∑ i, Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  have hφ : ∀ i, algebraMap L T.K (φ (d i)) = Polynomial.aeval (T.io a) (d i) := fun i => by
    show L.val (φ (d i)) = _
    rw [← Polynomial.aeval_algHom_apply L.val xa (d i)]
    rfl
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, hφ]
  exact hK

theorem frac_isAlgebraic_adjoin_j : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  intro Ω _ _ _ ε T a ha f
  obtain ⟨x, y, hy, hxy⟩ := T.io_surj f
  have hy' : T.io y ≠ 0 := fun h => hy (T.io_inj (h.trans (map_zero T.io).symm))
  have hf : f = T.io x * (T.io y)⁻¹ := by rw [← hxy, mul_inv_cancel_right₀ hy']
  rw [hf]
  exact (isIntegral_io_adjoin_j Ω ε T a ha x).isAlgebraic.mul (isIntegral_io_adjoin_j Ω ε T a ha y).isAlgebraic.inv

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  atlas_forward_decl GlobalTheory.FN.frac_isAlgebraic_adjoin_j
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_const_and_quot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T
  have hmem := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs := fun a =>
    ((GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.1 _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ε.range _ ((hmem.1 _).1 a.2))
  refine ⟨fun c => ?_, fun f => ?_⟩
  · have hc : (fun _ : ℍ => ε c) ∈ ring ε.range := (hmem.1 _).2 (hmem.2 _ ⟨c, rfl⟩)
    rw [← T.io_c c ⟨_, hc⟩ rfl, T.an_io]
    rfl
  · obtain ⟨a, b, hb, h⟩ := T.io_surj f
    refine ⟨up (a : ℍ → ℂ), up (b : ℍ → ℂ), hdiff a, hdiff b, ?_, ?_⟩
    · intro h0
      have h1 : T.an (T.io b) = T.an (T.io 0) := by
        rw [T.an_io, map_zero, map_zero]; exact h0
      exact hb (T.io_inj ((GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.2.2 h1))
    · have := congrArg T.an h
      rw [map_mul, T.an_io, T.an_io] at this
      exact this

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_const_and_quotient : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  atlas_forward_decl GlobalTheory.FN.frac_const_and_quot
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_exp_converges : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (f : T.K), Den (T.exp f) ∧ ∃ (φ : ℂ → ℂ) (C : ℝ), T.an f = (φ : Mero) ∧ HS ε C φ (T.exp f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb0, hfab⟩ := T.io_surj f
  have hiob : T.io b ≠ 0 := by
    intro h
    exact hb0 (T.io_inj (by rw [h, map_zero]))
  have hexb : T.exp (T.io b) ≠ 0 := by
    intro h
    exact hiob (T.exp.toRingHom.injective (by simpa using h))
  have hexpf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hfab, map_mul, mul_assoc, mul_inv_cancel₀ hexb, mul_one]
  obtain ⟨hops, -, -, -, hinv⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  have hEa := T.exp_io a
  have hEb := T.exp_io b
  have hEbi := hinv _ _ hexb hEb
  have hE : IsExp ε ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹) (T.exp f) := by
    rw [hexpf]; exact (hops _ _ _ _ hEa hEbi).2.2
  obtain ⟨hden, C, hC⟩ := hE
  refine ⟨hden, up ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹), C, ?_, hC⟩

  obtain ⟨⟨A, hA⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  have hbR : InR ε.range (b : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 b.2
  have hbhol : DifferentiableOn ℂ (up (b : ℍ → ℂ)) Hs := (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ hbR)
  have hgb0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) ≠ 0 := by
    intro h
    apply hb0
    have h0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h
    have := hid _ _ hbhol (differentiableOn_const 0) h0
    apply Subtype.ext
    funext τ
    have h1 := this τ (hHs τ)
    simpa [up, UpperHalfPlane.ofComplex_apply] using h1
  have hev := (hunit _ hbhol hgb0).1
  have hgi : germ ((b : ℍ → ℂ)⁻¹) * germ (b : ℍ → ℂ) = 1 := by
    unfold germ
    rw [← Filter.Germ.coe_mul]
    show ((up ((b : ℍ → ℂ)⁻¹) * up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (1 : ℂ) : ℂ → ℂ) : Mero)
    rw [Filter.Germ.coe_eq]
    filter_upwards [hev] with z hz
    simp only [Pi.mul_apply, up, Pi.inv_apply] at hz ⊢
    exact inv_mul_cancel₀ hz
  have hanf : T.an f * germ (b : ℍ → ℂ) = germ (a : ℍ → ℂ) := by
    rw [← T.an_io, ← T.an_io, ← map_mul, hfab]
  show T.an f = germ ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹)
  rw [← hA, map_mul, hA, hA, ← hanf, mul_assoc, mul_comm (germ (b : ℍ → ℂ)), hgi, mul_one]

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_expansion_converges : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), Den (T.exp f) ∧ ∃ (φ : ℂ → ℂ) (C : ℝ), T.an f = (φ : Mero) ∧ HS ε C φ (T.exp f) := by
  atlas_forward_decl GlobalTheory.FN.frac_exp_converges
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def germCompMob (g : GQ) : Mero →+* Mero where
  toFun F := F.compTendsto (mob g) (GlobalTheory.T.tendsto_mob_codiscreteWithin_codiscreteWithin g)
  map_one' := rfl
  map_mul' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl
  map_zero' := rfl
  map_add' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl

theorem germCompMob_coe (g : GQ) (φ : ℂ → ℂ) :
    germCompMob g (φ : Mero) = ((fun z => φ (mob g z)) : Mero) := rfl

theorem an_sl_germ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ) (f : T.K) (φ : ℂ → ℂ), T.an f = (φ : Mero) → T.an (T.sl g f) = ((fun z => φ (mob g z)) : Mero) := by
  intro Ω _ _ _ ε T g f φ hf
  have key : T.an.comp ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) = (germCompMob g).comp T.an := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1 Mero
    intro a
    obtain ⟨a', ha', hs⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    simp only [RingHom.comp_apply]
    rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) (T.io a) = T.sl g (T.io a) from rfl, hs, T.an_io, T.an_io]
    unfold germ
    rw [germCompMob_coe]
    apply (GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.2.1
    intro z hz
    rw [ha']
    exact (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz
  have h2 := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at h2
  rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) f = T.sl g f from rfl] at h2
  rw [h2, hf, germCompMob_coe]

end GlobalTheory.FN
end
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_an_sl_germ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ) (f : T.K) (φ : ℂ → ℂ), T.an f = (φ : Mero) → T.an (T.sl g f) = ((fun z => φ (mob g z)) : Mero) := by
  atlas_forward_decl GlobalTheory.FN.an_sl_germ
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FNExpJ

variable {Ω : Type} [Field Ω]

theorem ofPowerSeries_coeff_of_ne (P : PowerSeries Ω) {r : ℚ} (hr : ∀ n : ℕ, (n : ℚ) ≠ r) :
    (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n, -, hn⟩
  exact hr n (by simpa using hn)

theorem expansion_j : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω,
    IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧
      ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  obtain ⟨c, hc⟩ := GlobalTheory.exists_hasSum_modularJ_sub_inv
  set P : PowerSeries Ω := PowerSeries.mk fun n => (c n : Ω) with hPdef
  have hP : ∀ n : ℕ, (HahnSeries.ofPowerSeries ℚ Ω P).coeff (n : ℚ) = (c n : Ω) := fun n => by
    rw [HahnSeries.ofPowerSeries_apply_coeff, hPdef, PowerSeries.coeff_mk]
  have h0 : ∀ r : ℚ, (∀ n : ℕ, (n : ℚ) ≠ r) → (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 :=
    fun r hr => ofPowerSeries_coeff_of_ne P hr
  have hneg : ∀ r : ℚ, r < 0 → ∀ n : ℕ, (n : ℚ) ≠ r := fun r hr n hn => by
    have : (0 : ℚ) ≤ n := n.cast_nonneg
    linarith
  refine ⟨HahnSeries.single (-1 : ℚ) (1 : Ω) + HahnSeries.ofPowerSeries ℚ Ω P,
    ⟨?_, 0, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨1, one_pos, fun r hr => ?_⟩
    by_cases h1 : r = -1
    · exact ⟨-1, by simp [h1]⟩
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      exact ⟨n, by simp⟩
    · push_neg at h2
      exfalso
      apply hr
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2, add_zero]
  · intro z hz
    set τ : ℍ := ⟨z, hz⟩ with hτ
    have hup : up jT z = GlobalTheory.modularJ τ := by
      simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rfl
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * z) := by
      simp [Function.Periodic.qParam, hτ]
    have H1 : HasSum (fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ := by
      have := hasSum_single (f := fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (-1) (fun r hr => by
          simp [HahnSeries.coeff_single_of_ne hr])
      convert this using 1
      rw [hq, HahnSeries.coeff_single_same, map_one, one_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    have H2 : HasSum (fun r : ℚ => ε ((HahnSeries.ofPowerSeries ℚ Ω P).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z))
        (GlobalTheory.modularJ τ - (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) := by
      refine (Function.Injective.hasSum_iff (g := fun n : ℕ => (n : ℚ)) Nat.cast_injective
        (fun r hr => ?_)).mp ?_
      · rw [h0 r (fun n hn => hr ⟨n, hn⟩), map_zero, zero_mul]
      · convert hc τ using 1
        funext n
        simp only [Function.comp_apply, hP, map_intCast, hq, ← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring
    convert H1.add H2 using 1
    · funext r
      rw [HahnSeries.coeff_add, map_add, add_mul]
    · rw [hup]
      ring
  · rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num)), add_zero]
  · intro r hr
    rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne hr.ne, h0 r (hneg r (by linarith)),
      add_zero]
  · intro r
    by_cases h1 : r = -1
    · subst h1
      refine ⟨1, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num))]
      simp
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      refine ⟨c n, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, hP, zero_add]
    · push_neg at h2
      exact ⟨0, by rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2]; simp⟩

end GlobalTheory.FNExpJ
end
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_cuspExpansion_jInvariant : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  atlas_forward_decl GlobalTheory.FNExpJ.expansion_j
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem j_in_frac : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), ∃ a : GlobalTheory.FN.ring ε.range, (a : ℍ → ℂ) = jT ∧ (∀ γ : SL(2, ℤ), T.sl (ofSL γ) (T.io a) = T.io a) ∧ (T.exp (T.io a)).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (T.exp (T.io a)).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (T.exp (T.io a)).coeff r = n := by
  intro Ω _ _ _ ε T
  have hlv := (GlobalTheory.T.lv_jT_one_and_jT_smul_eq ε.range).1
  let a : GlobalTheory.FN.ring ε.range := ⟨jT, mem_ring_of_inR ⟨1, 1, one_pos, hlv⟩⟩
  have ha : (a : ℍ → ℂ) = jT := rfl
  obtain ⟨h, hexp, h1, h2, h3⟩ := GlobalTheory.T.exists_integral_cuspExpansion_jInvariant Ω ε
  have heq : T.exp (T.io a) = h :=
    (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 jT _ _ (T.exp_io a) hexp
  refine ⟨a, ha, fun γ => ?_, ?_, ?_, ?_⟩
  · apply T.sl_io
    rw [ha, (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.1 γ jT]
    funext τ
    exact ((GlobalTheory.T.lv_jT_one_and_jT_smul_eq ε.range).2 γ τ).symm
  · rw [heq]; exact h1
  · rw [heq]; exact h2
  · rw [heq]; exact h3

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jInvariant_in_modularFunctionFractionField : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), ∃ a : GlobalTheory.FN.ring ε.range, (a : ℍ → ℂ) = jT ∧ (∀ γ : SL(2, ℤ), T.sl (ofSL γ) (T.io a) = T.io a) ∧ (T.exp (T.io a)).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (T.exp (T.io a)).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (T.exp (T.io a)).coeff r = n := by
  atlas_forward_decl GlobalTheory.FN.j_in_frac
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem sl_ofSL_io_of_gamma {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) (a : ring ε.range) (M : ℕ)
    (ha : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, (a : ℍ → ℂ) (γ • τ) = (a : ℍ → ℂ) τ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M) : T.sl (ofSL γ) (T.io a) = T.io a := by
  apply T.sl_io
  rw [GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.2.1 γ a]
  funext τ
  exact (ha γ hγ τ).symm

theorem frac_exists_level (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K) :
    ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f := by
  obtain ⟨a, b, hb, hf⟩ := T.io_surj f
  obtain ⟨N₁, w₁, hN₁, h₁⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2
  obtain ⟨N₂, w₂, hN₂, h₂⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2
  have hM : 0 < N₁ * N₂ := Nat.mul_pos hN₁ hN₂
  have h₁' := GlobalTheory.T.lv_mono_of_dvd_of_le ε.range N₁ (N₁ * N₂) w₁ w₁ a hM (dvd_mul_right _ _) le_rfl h₁
  have h₂' := GlobalTheory.T.lv_mono_of_dvd_of_le ε.range N₂ (N₁ * N₂) w₂ w₂ b hM (dvd_mul_left _ _) le_rfl h₂
  refine ⟨N₁ * N₂, hM, fun γ hγ => ?_⟩
  have ea := sl_ofSL_io_of_gamma T a _ h₁'.1 γ hγ
  have eb := sl_ofSL_io_of_gamma T b _ h₂'.1 γ hγ
  have hib : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have key : T.sl (ofSL γ) f * T.io b = f * T.io b := by
    have := congrArg (T.sl (ofSL γ)) hf
    rw [map_mul, eb, ea] at this
    rw [this, hf]
  exact mul_right_cancel₀ hib key

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionField_exists_gamma_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f := by
  atlas_forward_decl GlobalTheory.FN.frac_exists_level
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem laurent_exp_shift (M : ℕ) (hM : 0 < M) (w : ℕ) (k : ℤ) (τ : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * ((k - (w * M : ℕ) : ℤ) : ℂ) * τ / M) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem laurent_qAll_int (E : Subring ℂ) (M : ℕ) (hM : 0 < M) (f : ℍ → ℂ) (c : ℕ → ℤ)
    (h : HasQ 1 f fun n => (c n : ℂ)) : QAll (· ∈ E) M f :=
  QAll.of_dvd hM (one_dvd M) E.zero_mem ⟨_, h, fun n => intCast_mem E (c n)⟩

theorem laurent_iff : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  intro E M φ hM
  obtain ⟨⟨cD, -, hD⟩, ⟨cI, -, hI⟩⟩ := GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions
  obtain ⟨-, -, -, hmul, hpow, -⟩ := GlobalTheory.QFam.QAllSubring.ring_closed E M hM
  have hqD := laurent_qAll_int E M hM _ cD hD
  have hqI := laurent_qAll_int E M hM _ cI hI
  have hDD0 : ∀ τ : ℍ, DD τ ≠ 0 := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb, hbE⟩ := hmul _ _ (hpow _ w hqI) hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    let c : ℤ → ℂ := fun n => if -((w * M : ℕ) : ℤ) ≤ n then b (n + ((w * M : ℕ) : ℤ)).toNat else 0
    refine ⟨c, -((w * M : ℕ) : ℤ), fun n => ?_, fun n hn => ?_, fun τ => ?_⟩
    · simp only [c]
      split_ifs
      · exact hbE _
      · exact E.zero_mem
    · simp only [c]
      rw [if_neg (not_le.mpr hn)]
    · rw [← hginj.hasSum_iff]
      · have h1 := (hb τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹
        have hφ : (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            ((Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) ^ w * (DD τ ^ w * φ τ)) = φ τ := by
          rw [div_pow]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))),
            pow_ne_zero w (hDD0 τ)]
        rw [hφ] at h1
        have key : (fun k : ℕ => (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            (b k * Complex.exp (2 * Real.pi * Complex.I * k * τ / M))) =
            (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) ∘ g := by
          funext k
          simp only [Function.comp, g, c]
          rw [if_pos (by omega)]
          have hk : ((k : ℤ) - ((w * M : ℕ) : ℤ) + ((w * M : ℕ) : ℤ)).toNat = k := by omega
          rw [hk]
          have := laurent_exp_shift M hM w k τ
          rw [← Int.cast_natCast k, ← this]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
        rw [key] at h1
        exact h1
      · intro n hn
        have : ¬ (-((w * M : ℕ) : ℤ) ≤ n) := fun h => hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by
          simp only [g]; omega⟩
        simp only [c]
        rw [if_neg this, zero_mul]
  · rintro ⟨c, n₀, hcE, hc0, hs⟩
    refine ⟨(-n₀).toNat, ?_⟩
    set w := (-n₀).toNat with hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    have hwM : (w : ℤ) ≤ ((w * M : ℕ) : ℤ) := by
      have : w ≤ w * M := Nat.le_mul_of_pos_right w hM
      exact_mod_cast this
    have hq : HasQ M (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ) fun k => c (g k) := by
      intro τ
      have h1 := (hs τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)
      rw [← hginj.hasSum_iff] at h1
      · have key : (fun i : ℤ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / M))) ∘ g =
            fun k : ℕ => c (g k) * Complex.exp (2 * Real.pi * Complex.I * k * τ / M) := by
          funext k
          simp only [Function.comp, g]
          rw [mul_left_comm, laurent_exp_shift M hM w k τ]
          push_cast
          rfl
        rw [key] at h1
        exact h1
      · intro n hn
        have : n < n₀ := by
          by_contra hh
          exact hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by simp only [g]; omega⟩
        simp [hc0 n this]
    have hqE : QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ :=
      ⟨_, hq, fun k => hcE _⟩
    have h2 := hmul _ _ (hpow _ w hqD) hqE
    have key : (fun τ : ℍ => (DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) ^ w *
        (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ)) = fun τ => DD τ ^ w * φ τ := by
      funext τ
      rw [div_pow]
      field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
    rw [key] at h2
    exact h2

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  atlas_forward_decl GlobalTheory.FN.laurent_iff
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem uniform_pole_order : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) →
    (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  intro E M f hM hinv hw
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  choose w hw using hw
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let lift : SL(2, ZMod M) → SL(2, ℤ) := fun g => if h : ∃ γ, red γ = g then h.choose else 1
  let W : ℕ := Finset.univ.sup fun g => w (lift g)
  refine ⟨W, hinv, fun γ => ?_⟩
  have hex : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
  have hl : lift (red γ) = hex.choose := dif_pos hex
  set γ' := lift (red γ) with hγ'
  have hred : red γ' = red γ := by rw [hl]; exact hex.choose_spec
  have hmem : γ * γ'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem']
    show red (γ * γ'⁻¹) = 1
    rw [map_mul, map_inv, hred, mul_inv_cancel]
  have hf : ∀ τ : ℍ, f (γ • τ) = f (γ' • τ) := fun τ => by
    have := hinv _ hmem (γ' • τ)
    rw [← this, ← mul_smul, inv_mul_cancel_right]
  have hle : w γ' ≤ W := Finset.le_sup (f := fun g => w (lift g)) (Finset.mem_univ (red γ))
  have hD : QAll (· ∈ E) M fun τ => DD τ ^ (W - w γ') :=
    QAllSubring.pow _ (eis_qAll M hM DD (Or.inr (Or.inr rfl)) E)
  have := QAllSubring.mul hD (hw γ')
  convert this using 2 with τ
  rw [hf τ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) → (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  atlas_forward_decl GlobalTheory.FN.uniform_pole_order
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_of_qexp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  intro Ω _ _ _ ε T a M hM _ hinv hexp
  have hHs : ∀ τ : ℍ, (τ : ℂ) ∈ Hs := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.2
  have hmob : ∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.2.2.1
  set f : ℍ → ℂ := fun τ => a τ with hf
  have hinvf : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ := by
    intro γ hγ τ
    simp only [hf]
    rw [← hmob γ τ]
    exact hinv γ hγ τ (hHs τ)
  have hw : ∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ ε.range) M fun τ => DD τ ^ w * f (γ • τ) := by
    intro γ
    obtain ⟨c, n0, hc0, hs⟩ := hexp γ
    refine (GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries ε.range M (fun τ => f (γ • τ)) hM).2 ⟨fun n => ε (c n), n0, fun n => ⟨c n, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp [hc0 n hn]
    · intro τ
      have := hs τ (hHs τ)
      simp only [hf]
      rw [← hmob γ τ]
      exact this
  obtain ⟨w, hLv⟩ := GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll ε.range M f hM hinvf hw
  have hmem : f ∈ ring ε.range := mem_ring_of_inR ⟨M, w, hM, hLv⟩
  refine ⟨T.io ⟨f, hmem⟩, ?_⟩
  rw [T.an_io]
  exact GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.1 a

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  atlas_forward_decl GlobalTheory.FN.exists_of_qexp
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.Sat

theorem mdiff_comp_sl (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f (γ • τ)) := by
  have hg : 0 < ((γ : GL (Fin 2) ℝ)).det.val := by simp
  exact hf.comp (UpperHalfPlane.mdifferentiable_smul hg)

theorem gamma_le {K L : ℕ} (hd : K ∣ L) : CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  have c : ∀ x y : ℤ, ((x : ZMod L) = y) → ((x : ZMod K) = y) := fun x y h => by
    have := congrArg (ZMod.castHom hd (ZMod K)) h
    simpa using this
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ 1 (by simpa using h1)
  · simpa using c _ 0 (by simpa using h2)
  · simpa using c _ 0 (by simpa using h3)
  · simpa using c _ 1 (by simpa using h4)

theorem alg (m : ℕ) (P : ℕ → ℂ) (x y : ℂ)
    (h : ∑ i ∈ Finset.range (m + 1 + 1), P i * x ^ i * y ^ (m + 1 - i) = 0) :
    (P (m + 1) * x) ^ (m + 1) +
      ∑ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) = 0 := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
  have key : ∀ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) =
      P (m + 1) ^ m * (P j * x ^ (j : ℕ) * y ^ (m + 1 - j)) := by
    intro j
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp j.isLt)
    have e1 : m - j = k := by omega
    have e2 : P (m + 1) ^ m = P (m + 1) ^ k * P (m + 1) ^ (j : ℕ) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, mul_pow]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have : (P (m + 1) * x) ^ (m + 1) = P (m + 1) ^ m * (P (m + 1) * x ^ (m + 1) * y ^ (m + 1 - (m + 1))) := by
    simp only [Nat.sub_self, pow_zero, mul_one]; ring
  rw [this]
  linear_combination (P (m + 1) ^ m) * h

theorem sat : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  intro Ω _ _ ε M n a b p hM ha hb hb0 hab hp hpn heq
  obtain ⟨-, hiff, -, -, hmem⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hring := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have inR_mul : ∀ f g : ℍ → ℂ, InR ε.range f → InR ε.range g → InR ε.range (f * g) := fun f g hf hg =>
    (hring.1 _).1 (Subring.mul_mem _ ((hring.1 _).2 hf) ((hring.1 _).2 hg))
  have inR_pow : ∀ (f : ℍ → ℂ) (k : ℕ), InR ε.range f → InR ε.range (f ^ k) := fun f k hf =>
    (hring.1 _).1 (Subring.pow_mem _ ((hring.1 _).2 hf) k)
  have hol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p i) := fun i => GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hp i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso; apply hpn; funext τ; have := heq τ; simpa using this
    · exact ⟨m, rfl⟩
  have hHs : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}; exact isOpen_lt continuous_const Complex.continuous_im
  have hHc : IsPreconnected Hs := by
    apply Convex.isPreconnected
    show Convex ℝ {z : ℂ | 0 < z.im}
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases hs.eq_or_lt with rfl | hs'
    · simp at hst; subst hst; simpa using hy
    · nlinarith [mul_pos hs' hx, mul_nonneg ht hy.le]
  have dOn : ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → DifferentiableOn ℂ (up f) Hs := fun f hf => (hiff f).1 hf
  have upc : ∀ (f : ℍ → ℂ) (τ : ℍ), up f (τ : ℂ) = f τ := fun f τ => by
    simp only [up, UpperHalfPlane.ofComplex_apply]
  obtain ⟨τ0, hτ0⟩ : ∃ τ, b τ ≠ 0 := by
    by_contra hc; push_neg at hc; exact hb0 (funext hc)
  obtain ⟨h', hh'd, hAD, hmon⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral Hs (m + 1) (fun z => up (p (m + 1)) z * up a z) (up b)
    (fun j z => up (p j) z * up (p (m + 1)) z ^ (m - j)) hHs hHc
    ((dOn _ (hol _)).mul (dOn _ ha)) (dOn _ hb) (fun j => (dOn _ (hol _)).mul ((dOn _ (hol _)).pow _))
    ⟨τ0, hmem τ0, by rw [upc]; exact hτ0⟩
    (fun z _ => alg m (fun i => p i (UpperHalfPlane.ofComplex z)) (a (UpperHalfPlane.ofComplex z))
      (b (UpperHalfPlane.ofComplex z)) (heq _))
  set h : ℍ → ℂ := fun τ => h' τ with hh
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hiff]
    refine hh'd.congr fun z hz => ?_
    show h' (UpperHalfPlane.ofComplex z : ℂ) = h' z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hPA : ∀ τ, p (m + 1) τ * a τ = h τ * b τ := fun τ => by
    have := hAD τ (hmem τ); simpa only [upc] using this
  obtain ⟨N, w, hN, hLv, -⟩ := hp (m + 1)
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (M * N), ∀ τ : ℍ, h (γ • τ) = h τ := by
    intro γ hγ
    have hγM := gamma_le (Dvd.intro N rfl) hγ
    have hγN := gamma_le (Dvd.intro_left M rfl) hγ
    have hprod : ∀ τ, (fun τ => h (γ • τ) - h τ) τ * (fun τ => b τ * b (γ • τ)) τ = 0 := by
      intro τ
      have E1 := hPA (γ • τ)
      have E2 := hPA τ
      have E3 := hLv γ hγN τ
      have E4 := hab γ hγM τ
      simp only
      linear_combination (-(b τ)) * E1 + b (γ • τ) * E2 + (a (γ • τ) * b τ) * E3 + p (m + 1) τ * E4
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ ((mdiff_comp_sl h hhol γ).sub hhol) (hb.mul (mdiff_comp_sl b hb γ)) hprod with h0 | h0
    · intro τ; have := congrFun h0 τ; simpa [sub_eq_zero] using this
    · exfalso
      have hbb : ∀ τ, b τ * (fun τ => b (γ • τ)) τ = 0 := fun τ => congrFun h0 τ
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ hb (mdiff_comp_sl b hb γ) hbb with h1 | h1
      · exact hb0 h1
      · apply hτ0
        have := congrFun h1 (γ⁻¹ • τ0)
        simpa using this
  refine ⟨h, ?_, hPA⟩
  refine GlobalTheory.T.hasSomeLevelOver_of_integral_invariant Ω ε (M * N) (m + 1) h (fun j τ => p j τ * p (m + 1) τ ^ (m - j)) (Nat.mul_pos hM hN)
    hhol hinv (fun j => inR_mul _ _ (hp _) (inR_pow _ _ (hp _))) ?_
  intro τ
  have := hmon τ (hmem τ)
  simpa only [upc] using this

end GlobalTheory.FN.Sat
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturation_levelFunctions_integralRelation : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  atlas_forward_decl GlobalTheory.FN.Sat.sat
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧
      ∀ i, T.io (p i) = u * P.coeff i := by
  intro Ω _ _ _ ε T P hP
  classical
  choose a b hb hab using T.io_surj
  set S := Finset.range (P.natDegree + 1) with hS
  have hbne : ∀ f, T.io (b f) ≠ 0 := fun f h => hb f (T.io_inj (by rw [h, map_zero]))
  refine ⟨fun i => if i ∈ S then a (P.coeff i) * ∏ j ∈ S.erase i, b (P.coeff j) else 0,
    T.io (∏ j ∈ S, b (P.coeff j)), ?_, ?_, ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun j _ => hbne _
  · have hmem : P.natDegree ∈ S := by simp [hS]
    intro h
    simp only [hmem, if_true] at h
    have h2 := congrArg T.io h
    rw [map_zero, map_mul, ← hab, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hmem] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hP (Polynomial.leadingCoeff_eq_zero.mp h3)
    · exact (Finset.prod_ne_zero_iff.mpr fun j _ => hbne _) h3
  · intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [map_mul, ← hab, map_prod, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hi, mul_comm]
    · simp only [hi, if_false, map_zero]
      have : P.natDegree < i := by simp [hS] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, mul_zero]

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧ ∀ i, T.io (p i) = u * P.coeff i := by
  atlas_forward_decl GlobalTheory.FN.clear_denominators
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_sat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T a b M hM ha hb hb0 hinv ⟨P, hP, hPe⟩
  obtain ⟨_, hMD, hAE, _, hmemHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨hNT, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  obtain ⟨hmapsto, _, _, hmobSL, hmobD, _⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨p, u, hu, hpn, hp⟩ := GlobalTheory.T.modularFunctionFractionField_clear_denominators Ω ε T P hP
  set n := P.natDegree with hn
  have hR : ∀ i, InR ε.range (p i : ℍ → ℂ) := fun i => ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 (p i).2
  have hpD : ∀ i, DifferentiableOn ℂ (up (p i : ℍ → ℂ)) Hs := fun i => (hMD _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hR i))

  have hup : ∀ (g : ℂ → ℂ) (z : ℂ), z ∈ Hs → up (fun τ : ℍ => g τ) z = g z := by
    intro g z hz
    simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  have hupT : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp [up]

  have hxb : (((a / b : ℂ → ℂ)) : Mero) * (b : Mero) = (a : Mero) := by
    rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    filter_upwards [(hunit b hb hb0).1] with z hz
    simp [div_mul_cancel₀ _ hz]

  have hsum : ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i = 0 := by
    calc _ = T.an u * P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) := by
          rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hp i, map_mul, mul_assoc]
      _ = 0 := by rw [hPe, mul_zero]
  set F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) z * a z ^ i * b z ^ (n - i) with hF
  have e2 : F = ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) := by
    funext z; simp [hF, Finset.sum_apply]
  have hFg : (F : Mero) = 0 := by
    have e1 : (F : Mero) = Filter.Germ.coeRingHom _ F := rfl
    rw [e1, e2, map_sum]
    change ∑ i ∈ _, ((up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) : ℂ → ℂ) : Mero) = _
    simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
    calc _ = (b : Mero) ^ n * ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [T.an_io, ← hxb]
          show (up (p i : ℍ → ℂ) : Mero) * _ * _ = _ * ((up (p i : ℍ → ℂ) : Mero) * _)
          rw [mul_pow, mul_assoc, mul_assoc, ← pow_mul_pow_sub (b : Mero) hin]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  have hFD : DifferentiableOn ℂ F Hs := by
    rw [e2]
    refine DifferentiableOn.sum fun i _ => ?_
    exact ((hpD i).mul (ha.pow i)).mul (hb.pow (n - i))
  have hF0 : ∀ z ∈ Hs, F z = 0 := by
    have := hid F (fun _ => 0) hFD (differentiableOn_const 0) (by rw [hFg]; rfl)
    exact this

  have haM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => a τ) := (hMD _).2 (ha.congr fun z hz => hup a z hz)
  have hbM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => b τ) := (hMD _).2 (hb.congr fun z hz => hup b z hz)
  have hbne : (fun τ : ℍ => b τ) ≠ 0 := by
    intro h0
    apply hb0
    have : (b : Mero) = ((0 : ℂ → ℂ) : Mero) := hAE b 0 fun z hz => by
      simpa using congrFun h0 ⟨z, hz⟩
    rw [this]; rfl
  have hinvT : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a ((γ • τ : ℍ) : ℂ) * b τ = a τ * b ((γ • τ : ℍ) : ℂ) := by
    intro γ hγ τ
    have hmD : DifferentiableOn ℂ (mob (ofSL γ)) Hs := hmobD _
    have hmap : Set.MapsTo (mob (ofSL γ)) Hs Hs := fun z hz => hmapsto _ z hz
    have h1 : DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z) * b z) Hs := (ha.comp hmD hmap).mul hb
    have h2 : DifferentiableOn ℂ (fun z => a z * b (mob (ofSL γ) z)) Hs := ha.mul (hb.comp hmD hmap)
    have := hid _ _ h1 h2 (hinv γ hγ) τ (hmemHs τ)
    simpa [hmobSL] using this
  have hpn' : (p n : ℍ → ℂ) ≠ 0 := by
    intro h0; apply hpn; ext1; exact h0
  have hsumT : ∀ τ : ℍ, ∑ i ∈ Finset.range (n + 1), (p i : ℍ → ℂ) τ * (fun τ : ℍ => a τ) τ ^ i * (fun τ : ℍ => b τ) τ ^ (n - i) = 0 := by
    intro τ
    have := hF0 τ (hmemHs τ)
    simpa [hF, hupT] using this
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ)
  obtain ⟨h, hhR, hh⟩ := GlobalTheory.T.saturation_levelFunctions_integralRelation Ω ε M n (fun τ : ℍ => a τ) (fun τ : ℍ => b τ) (fun i => (p i : ℍ → ℂ)) hM haM hbM hbne
    hinvT hR hpn' hsumT
  let hr : ring ε.range := ⟨h, mem_ring_of_inR hhR⟩
  have hio0 : T.io (p n) ≠ 0 := by
    intro h0; apply hpn; exact T.io_inj (by rw [h0, map_zero])
  refine ⟨T.io hr / T.io (p n), ?_⟩
  have hg0 : (up (p n : ℍ → ℂ) : Mero) ≠ 0 := by
    intro h0
    have hinj : Function.Injective T.an := T.an.injective
    apply hio0; apply hinj; rw [map_zero, T.an_io]; exact h0
  have hU : IsUnit (up (p n : ℍ → ℂ) : Mero) := (hunit _ (hpD n) hg0).2
  have hrel : (up (p n : ℍ → ℂ) : Mero) * (a : Mero) = (up h : Mero) * (b : Mero) := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul]
    refine hAE _ _ fun z hz => ?_
    have e := hh ⟨z, hz⟩
    simp only [Pi.mul_apply]
    have q1 : up (p n : ℍ → ℂ) z = (p n : ℍ → ℂ) ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    have q2 : up h z = h ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    rw [q1, q2]; simpa using e
  have hf : T.an (T.io hr / T.io (p n)) * (up (p n : ℍ → ℂ) : Mero) = (up h : Mero) := by
    have : T.io hr / T.io (p n) * T.io (p n) = T.io hr := div_mul_cancel₀ _ hio0
    have := congrArg T.an this
    rw [map_mul, T.an_io, T.an_io] at this
    exact this
  apply hU.mul_left_cancel
  rw [hrel, ← hf]; ring

end GlobalTheory
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_saturation : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  atlas_forward_decl GlobalTheory.fn_sat
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem isExp_comp_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l →
    (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) →
    (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) →
    IsExp ε f h → IsExp ε f' h' := by
  intro Ω _ ε f f' l m h h' hl hf hc hexp
  obtain ⟨⟨N, hN, hden⟩, C, hC⟩ := hexp
  have hl0 : l ≠ 0 := hl.ne'
  refine ⟨⟨N * l.den, Nat.mul_pos hN l.den_pos, ?_⟩, max (C / l) 0, ?_⟩
  · intro s hs
    have hr : h.coeff (s / l) ≠ 0 := by
      intro h0
      apply hs
      have := hc (s / l)
      rw [div_mul_cancel₀ _ hl0, h0, map_zero, mul_zero] at this
      exact (map_eq_zero ε).1 this
    obtain ⟨n, hn⟩ := hden _ hr
    refine ⟨n * l.num, ?_⟩
    have hs' : s = s / l * l := by field_simp
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hd0 : (l.den : ℚ) ≠ 0 := by exact_mod_cast l.den_pos.ne'
    rw [hs', hn]
    push_cast
    rw [← Rat.mul_den_eq_num l]
    field_simp
  · intro z hz
    have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have hlz : C < ((l : ℂ) * z + (m : ℂ)).im := by
      have h1 : C / l < z.im := lt_of_le_of_lt (le_max_left _ _) hz
      have h2 : C < z.im * l := (div_lt_iff₀ (by exact_mod_cast hl)).1 h1
      simpa [mul_comm] using h2
    rw [hf z hz0]
    have key := hC _ hlz
    rw [← (Equiv.mulRight₀ l hl0).hasSum_iff]
    convert key using 1
    funext r
    have he : (Equiv.mulRight₀ l hl0) r = r * l := rfl
    simp only [Function.comp, he, hc r]
    rw [mul_comm (Complex.exp _) (ε (h.coeff r)), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l → (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) → (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) → IsExp ε f h → IsExp ε f' h' := by
  atlas_forward_decl GlobalTheory.FN.isExp_comp_affine
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_sl_coeff_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (T : Frac Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : T.K) (r : ℚ) :
    (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) =
      eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  obtain ⟨hl, hmob⟩ := (GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties).2.2.2.2.2 g hg
  obtain ⟨_, hε, h0, hadd, _, _⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (RingHom.id Ω) (ent g 0 0 / ent g 1 1)
    (fun r => eOm ε (r * (ent g 0 1 / ent g 1 1))) hl (by simpa using h0)
    (fun r r' => by simp only [add_mul, hadd])
  have key : (T.exp.toRingHom.comp (T.sl g).toRingEquiv.toRingHom) = Φ.comp T.exp.toRingHom := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1
    intro a
    obtain ⟨a', ha', hsl⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    have hE : IsExp ε a' (Φ (T.exp (T.io a))) := by
      refine GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine Ω ε a a' (ent g 0 0 / ent g 1 1) (ent g 0 1 / ent g 1 1) _ _ hl
        (fun z hz => ?_) (fun s => ?_) (T.exp_io a)
      · rw [ha', (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz, hmob z]
      · rw [hΦ, map_mul, hε]
        rfl
    have hu := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (T.exp_io a') hE
    show T.exp (T.sl g (T.io a)) = Φ (T.exp (T.io a))
    rw [hsl, hu]
  have hc := congrArg (fun h : HahnSeries ℚ Ω => h.coeff (r * (ent g 0 0 / ent g 1 1)))
    (RingHom.congr_fun key f)
  simp only [RingHom.comp_apply] at hc
  rw [mul_div_assoc, mul_div_assoc]
  refine (show (T.exp (T.sl g f)).coeff (r * (ent g 0 0 / ent g 1 1)) = _ from hc).trans ?_
  rw [hΦ]
  rfl

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ (f : T.K) (r : ℚ), (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) = eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  atlas_forward_decl GlobalTheory.FN.exp_sl_coeff_upper
end

section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem tower_exists : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  intro Ω _ _ _ ε
  obtain ⟨T⟩ := GlobalTheory.T.modularFunctionFractionField_nonempty Ω ε
  obtain ⟨a, ha, hinv, h1, h2, h3⟩ := GlobalTheory.T.exists_jInvariant_in_modularFunctionFractionField Ω ε T
  have hgerm := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hj := GlobalTheory.T.lv_jT_one_and_jT_smul_eq
  have hhol : DifferentiableOn ℂ (up jT) Hs :=
    (hgerm.2.1 jT).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ⊤ jT ⟨1, 1, one_pos, (hj ⊤).1⟩)
  refine ⟨{ K := T.K, exp := T.exp, sl := T.sl, sl_one := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).1, sl_mul := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).2,
            gal := T.gal, gal_exp := T.gal_exp,
            an := T.an, an_c := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).1, an_sl := GlobalTheory.T.modularFunctionFractionField_an_sl_germ Ω ε T, an_mero := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).2,
            an_exp := fun f => (GlobalTheory.T.modularFunctionFractionField_expansion_converges Ω ε T f).2,
            level := GlobalTheory.T.fractionField_exists_gamma_level Ω ε T, exp_upper := GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular Ω ε T, recip := GlobalTheory.T.shimuraReciprocity_modularFunctionFractionField Ω ε T,
            jK := T.io a, j_inv := hinv, j_exp := ⟨h1, h2, h3⟩,
            j_hol := ⟨up jT, by rw [T.an_io, ha]; rfl, hhol⟩,
            alg_j := GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant Ω ε T a ha, bdd := GlobalTheory.T.modularFunctionFractionField_bounded_denominators Ω ε T, sat := GlobalTheory.T.modularFunctionFractionField_saturation Ω ε T,
            mem_q := GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions Ω ε T }, ?_⟩
  show T.an (T.io a) = germ jT
  rw [T.an_io, ha]

end GlobalTheory.FN
end
