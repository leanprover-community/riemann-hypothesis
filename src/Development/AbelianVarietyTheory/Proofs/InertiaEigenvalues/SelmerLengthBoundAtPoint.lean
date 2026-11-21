import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.AdmissibleDesigns.StatementOneBFromUnramified
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEuler
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusAndExponentModEq
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_equiv_local_galois_group : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_of_local_cohomology_shape : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  first | exact @GlobalTheory.jSpan_holds | exact GlobalTheory.jSpan_holds | (intros; apply GlobalTheory.jSpan_holds <;> assumption)
end

section
namespace GlobalTheory.FixedOfPower
open Polynomial

theorem fix_of_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (c : k) (hc : c ^ p = c) : τ c = c := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  let f : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hc' : ∃ a, f a = c := by
    by_contra hcon
    have hP0 : (X ^ p - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
    have hsub : insert c (Finset.univ.image f) ⊆ (X ^ p - X : k[X]).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hP0]
      show eval x (X ^ p - X) = 0
      rw [eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        rw [← map_pow, ZMod.pow_card]
    have hcard : (insert c (Finset.univ.image f)).card = p + 1 := by
      rw [Finset.card_insert_of_notMem (by simpa using hcon),
        Finset.card_image_of_injective _ f.injective, Finset.card_univ, ZMod.card]
    have hle := (Finset.card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' (X ^ p - X : k[X])))
    rw [hcard, FiniteField.X_pow_card_sub_X_natDegree_eq k hp1] at hle
    omega
  obtain ⟨a, rfl⟩ := hc'
  exact DFunLike.congr_fun (RingHom.ext_zmod (τ.comp f) f) a

theorem ringHom_apply_eq_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (N : ℕ) (hN : 0 < N) (z : k) (hz : z ^ p ^ N = z) :
    ∃ e : ℕ, τ z = z ^ p ^ e := by
  have : ExpChar k p := ExpChar.prime Fact.out
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  let g : k[X] := ∏ e ∈ Finset.range (M + 1), (X - C (z ^ p ^ e))
  have hg : g.map (frobenius k p) = g := by
    have e1 : ∀ e : ℕ, (z ^ p ^ e) ^ p = z ^ p ^ (e + 1) := fun e => by rw [← pow_mul, pow_succ]
    simp only [g, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      frobenius_def, e1]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun e => X - C (z ^ p ^ e)), hz, pow_zero,
      pow_one]
  have hcoef : ∀ i, (g.coeff i) ^ p = g.coeff i := by
    intro i
    have h := congrArg (fun q : k[X] => q.coeff i) hg
    simpa [Polynomial.coeff_map, frobenius_def] using h
  have hτ : g.map τ = g := by
    ext i
    rw [Polynomial.coeff_map]
    exact fix_of_pow p τ _ (hcoef i)
  have hz0 : g.eval z = 0 := by
    simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos M)) (by simp)
  have hτz : g.eval (τ z) = 0 := by
    rw [← hτ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hz0, map_zero]
  simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hτz
  obtain ⟨e, -, he⟩ := Finset.prod_eq_zero_iff.mp hτz
  exact ⟨e, sub_eq_zero.mp he⟩

end GlobalTheory.FixedOfPower
end

section
section
namespace GlobalTheory

open Polynomial

theorem ringHom_apply_eq_pow_of_pow_pow_eq_self :
    ∀ {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ), 0 < N →
      ∀ (z : k), z ^ p ^ N = z → ∃ e : ℕ, τ z = z ^ p ^ e := by
  first
  | exact @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | (apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow ..)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_apply_eq_pow_prime_pow : ∀ {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ), 0 < N → ∀ (z : k), z ^ p ^ N = z → ∃ e : ℕ, τ z = z ^ p ^ e := by
  atlas_forward_decl GlobalTheory.ringHom_apply_eq_pow_of_pow_pow_eq_self
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_of_compatible_zmod_pow' : ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)), (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) → ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  first | exact @GlobalTheory.exists_padicInt_of_compatible_zmod_pow | exact GlobalTheory.exists_padicInt_of_compatible_zmod_pow | (intros; apply GlobalTheory.exists_padicInt_of_compatible_zmod_pow <;> assumption)
end

section
section
namespace GlobalTheory

theorem padicInt_hom_normalize : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  intro G _ _ p _ χ hχ hadd g₀ hg₀
  classical
  have hex : ∃ n : ℕ, ∃ g, χ g ≠ 0 ∧ (χ g).valuation = n := ⟨_, g₀, hg₀, rfl⟩
  obtain ⟨g₁, hg₁, hv₁⟩ := Nat.find_spec hex
  have hmin : ∀ g, χ g ≠ 0 → (χ g₁).valuation ≤ (χ g).valuation := by
    intro g hg
    rw [hv₁]
    exact Nat.find_min' hex ⟨g, hg, rfl⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hle : ∀ g, ‖χ g‖ ≤ ‖χ g₁‖ := by
    intro g
    by_cases hg : χ g = 0
    · rw [hg, norm_zero]; exact norm_nonneg _
    rw [PadicInt.norm_eq_zpow_neg_valuation hg, PadicInt.norm_eq_zpow_neg_valuation hg₁]
    apply zpow_le_zpow_right₀ hp1
    have := hmin g hg
    omega
  have hn₁ : (χ g₁ : ℚ_[p]) ≠ 0 := fun h => hg₁ (PadicInt.coe_eq_zero.1 h)
  have hbd : ∀ g, ‖(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p])‖ ≤ 1 := by
    intro g
    rw [norm_div, div_le_one (norm_pos_iff.2 hn₁)]
    exact hle g
  refine ⟨fun g => ⟨(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]), hbd g⟩, ?_, ?_, ?_, g₁, ?_⟩
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp hχ).div_const _
  · intro g h
    apply Subtype.ext
    show ((χ (g * h) : ℚ_[p])) / (χ g₁ : ℚ_[p]) = (χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]) + (χ h : ℚ_[p]) / (χ g₁ : ℚ_[p])
    rw [hadd, PadicInt.coe_add, add_div]
  · intro g hg
    apply Subtype.ext
    simp [hg]
  · apply Subtype.ext
    simp [div_self hn₁]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_continuous_hom_normalize_one : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  atlas_forward_decl GlobalTheory.padicInt_hom_normalize
end

section
section
open ReciprocityTheory.Gal Pointwise NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_frob_at_place_over_prime : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω),
    A.valuation (p : Ω) < 1 → ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧
      ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  intro F Ω _ _ _ _ _ p hp A hpA
  set f : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F) with hf
  have fA : ∀ r : 𝓞 F, f r ∈ A := fun r =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe r).map (algebraMap F Ω).toIntAlgHom)
  let I : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal A).comap (f.codRestrict A fA)
  have memI : ∀ r, r ∈ I ↔ A.valuation (algebraMap F Ω (r : F)) < 1 := fun r => by
    simp only [I, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have hIp : I.IsPrime := Ideal.comap_isPrime _ _
  have hpI : (p : 𝓞 F) ∈ I := by
    rw [memI]; simpa using hpA
  have hIne : I ≠ ⊥ := fun h => by
    have h' := hpI
    rw [h, Ideal.mem_bot] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  let v : HeightOneSpectrum (𝓞 F) := ⟨I, hIp, hIne⟩
  obtain ⟨σ, hσA, hσ⟩ := exists_frob_over (F := F) (A := A) (v := v) (fun x => (memI x).symm)
  refine ⟨σ, hσA, Nat.card (𝓞 F ⧸ v.asIdeal), fun h1 => ?_, hσ⟩
  have hss : Subsingleton (𝓞 F ⧸ v.asIdeal) := by
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finite.card_le_one_iff_subsingleton.mp h1.le
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
  exact hIp.ne_top ((Ideal.eq_top_iff_one _).2 this)

end GlobalTheory
end

open ReciprocityTheory.Gal Pointwise NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frob_at_valuationSubring_over_prime : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 → ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧ ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  atlas_forward_decl GlobalTheory.exists_frob_at_place_over_prime
end

section
section
noncomputable section

open ReciprocityTheory.Gal Pointwise

namespace GlobalTheory.UnrChar

theorem frob_orbit {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ)
    (hN : 0 < N) (z : k) (hz : z ^ p ^ N = z) : ∃ e : ℕ, τ z = z ^ p ^ e :=
  GlobalTheory.T.exists_ringHom_apply_eq_pow_prime_pow p τ N hN z hz

theorem exists_padic_of_compat (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n))
    (hc : ∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) :
    ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n :=
  GlobalTheory.T.exists_padicInt_of_compatible_zmod_pow' p c hc

theorem exists_normalized {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime]
    (χ : G → ℤ_[p]) (hc : Continuous χ) (hadd : ∀ g h, χ (g * h) = χ g + χ h) (g₀ : G)
    (h₀ : χ g₀ ≠ 0) : ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧
      (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 :=
  GlobalTheory.T.padicInt_continuous_hom_normalize_one p χ hc hadd g₀ h₀

theorem exists_frob_ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω)
    (hp : A.valuation (p : Ω) < 1) : ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧
      ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 :=
  GlobalTheory.T.exists_frob_at_valuationSubring_over_prime A hp

theorem one_lt_pow_pow (p : ℕ) [Fact p.Prime] (n : ℕ) : 1 < p ^ p ^ n :=
  Nat.one_lt_pow (pow_pos (Fact.out : p.Prime).pos n).ne' (Fact.out : p.Prime).one_lt

theorem pow_pow_sub_one_ne_zero (p : ℕ) [Fact p.Prime] (n : ℕ) : p ^ p ^ n - 1 ≠ 0 := by
  have := one_lt_pow_pow p n; omega

theorem exists_primitive (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime]
    (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ p ^ n - 1) := by
  haveI : NeZero (p ^ p ^ n - 1) := ⟨pow_pow_sub_one_ne_zero p n⟩
  haveI : NeZero ((p ^ p ^ n - 1 : ℕ) : Ω) := inferInstance
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω _

theorem not_valuation_lt_one {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω)
    (hp : A.valuation (p : Ω) < 1) (n : ℕ) : ¬ A.valuation ((p ^ p ^ n - 1 : ℕ) : Ω) < 1 := by
  intro h
  have h1 : A.valuation ((p : Ω) ^ p ^ n) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hp (pow_pos (Fact.out : p.Prime).pos n).ne'
  have e : (1 : Ω) = (p : Ω) ^ p ^ n + -((p ^ p ^ n - 1 : ℕ) : Ω) := by
    rw [Nat.cast_sub (one_lt_pow_pow p n).le]; push_cast; ring
  have := Valuation.map_add_lt A.valuation h1 (by rw [Valuation.map_neg]; exact h)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

section main

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

def PowOn (p : ℕ) (g : Ω ≃ₐ[F] Ω) (n e : ℕ) : Prop :=
  ∀ x : Ω, x ^ (p ^ p ^ n - 1) = 1 → g x = x ^ p ^ e

theorem PowOn.mono {p : ℕ} {g : Ω ≃ₐ[F] Ω} {n₁ n₂ e : ℕ} (h : n₁ ≤ n₂) (he : PowOn p g n₂ e) :
    PowOn p g n₁ e := by
  intro x hx
  apply he
  obtain ⟨d, hd⟩ : p ^ p ^ n₁ - 1 ∣ p ^ p ^ n₂ - 1 := by
    have : p ^ p ^ n₂ = (p ^ p ^ n₁) ^ p ^ (n₂ - n₁) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' h]
    rw [this]; simpa using Nat.sub_dvd_pow_sub_pow (p ^ p ^ n₁) 1 (p ^ (n₂ - n₁))
  rw [hd, pow_mul, hx, one_pow]

theorem PowOn.mul {p : ℕ} {g h : Ω ≃ₐ[F] Ω} {n a b : ℕ} (hg : PowOn p g n a) (hh : PowOn p h n b) :
    PowOn p (g * h) n (a + b) := by
  intro x hx
  rw [AlgEquiv.mul_apply, hh x hx, hg _ (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]),
    ← pow_mul, pow_add, mul_comm (p ^ a)]

theorem PowOn.modEq [IsAlgClosed Ω] [CharZero Ω] {p : ℕ} [Fact p.Prime] {g : Ω ≃ₐ[F] Ω}
    {n a b : ℕ} (ha : PowOn p g n a) (hb : PowOn p g n b) : a ≡ b [MOD p ^ n] := by
  obtain ⟨ζ, hζ⟩ := exists_primitive Ω p n
  have h1 := (ha ζ hζ.pow_eq_one).symm.trans (hb ζ hζ.pow_eq_one)
  apply GlobalTheory.Cyc.modEq_of_pow_modEq_pow_sub_one p (p ^ n) a b (Fact.out : p.Prime).two_le
    (pow_pos (Fact.out : p.Prime).pos n)
  have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (pow_pow_sub_one_ne_zero p n)
  rw [hζ.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq.1 h1

variable [NumberField F] [IsAlgClosure F Ω]

theorem exists_powOn {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1)
    (g : A.decompositionSubgroup F) (n : ℕ) : ∃ e, PowOn p (g : Ω ≃ₐ[F] Ω) n e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hpp : p.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitive Ω p n
  have hm0 : p ^ p ^ n - 1 ≠ 0 := pow_pow_sub_one_ne_zero p n
  haveI : NeZero (p ^ p ^ n - 1) := ⟨hm0⟩
  have hζm : ζ ^ (p ^ p ^ n - 1) = 1 := hζ.pow_eq_one
  have hgm : ((g : Ω ≃ₐ[F] Ω) ζ) ^ (p ^ p ^ n - 1) = 1 := by rw [← map_pow, hζm, map_one]
  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp (valuation_eq_one_of_pow_eq_one A hm0 hζm).le
  let a : A := ⟨ζ, hζA⟩
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    rw [CharP.charP_iff_prime_eq_zero hpp]
    have : ((p : A)) ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff _).mpr (by simpa using hp)
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]; exact this
  have hz : (IsLocalRing.residue A a) ^ p ^ p ^ n = IsLocalRing.residue A a := by
    rw [← map_pow]; congr 1; apply Subtype.ext
    show ζ ^ p ^ p ^ n = ζ
    rw [← Nat.sub_add_cancel (one_lt_pow_pow p n).le, pow_succ, hζm, one_mul]
  obtain ⟨e, he⟩ := frob_orbit p (MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g)
    (p ^ n) (pow_pos hpp.pos n) _ hz
  have h2 : IsLocalRing.residue A (g • a - a ^ p ^ e) = 0 := by
    rw [map_sub, IsLocalRing.ResidueField.residue_smul, map_pow, sub_eq_zero]; exact he
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
  have e2 : ((g • a - a ^ p ^ e : A) : Ω) = (g : Ω ≃ₐ[F] Ω) ζ - ζ ^ p ^ e := rfl
  rw [e2] at h2
  have hgζ : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ p ^ e := by
    refine eq_of_pow_eq_one A (not_valuation_lt_one A hp n) hgm ?_ h2
    rw [← pow_mul, mul_comm, pow_mul, hζm, one_pow]
  refine ⟨e, fun x hx => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hgζ, ← pow_mul, ← pow_mul, mul_comm]

theorem main {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧
        ∃ g, χ g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hpp : p.Prime := Fact.out
  choose E hE using fun (g : A.decompositionSubgroup F) n => exists_powOn A hp g n
  have compat : ∀ (g : A.decompositionSubgroup F) n₁ n₂ (h : n₁ ≤ n₂),
      ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) ((E g n₂ : ℕ) : ZMod (p ^ n₂)) =
        ((E g n₁ : ℕ) : ZMod (p ^ n₁)) := by
    intro g n₁ n₂ h
    rw [map_natCast, ZMod.natCast_eq_natCast_iff]
    exact PowOn.modEq ((hE g n₂).mono h) (hE g n₁)
  choose χ' hχ' using fun g : A.decompositionSubgroup F =>
    exists_padic_of_compat p (fun n => ((E g n : ℕ) : ZMod (p ^ n))) (compat g)
  have key : ∀ (g : A.decompositionSubgroup F) n e, PowOn p (g : Ω ≃ₐ[F] Ω) n e →
      PadicInt.toZModPow n (χ' g) = (e : ZMod (p ^ n)) := by
    intro g n e he
    rw [hχ' g n, ZMod.natCast_eq_natCast_iff]
    exact PowOn.modEq (hE g n) he
  have hadd : ∀ g h : A.decompositionSubgroup F, χ' (g * h) = χ' g + χ' h := by
    intro g h
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [key (g * h) n _ ((hE g n).mul (hE h n)), map_add, hχ' g n, hχ' h n, Nat.cast_add]
  have hine : ∀ g : A.decompositionSubgroup F, (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ' g = 0 := by
    intro g hg
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [map_zero, key g n 0 ?_, Nat.cast_zero]
    intro x hx
    rw [pow_zero, pow_one]
    refine eq_of_pow_eq_one A (not_valuation_lt_one A hp n) (by rw [← map_pow, hx, map_one]) hx ?_
    exact hg.2 x (valuation_eq_one_of_pow_eq_one A (pow_pow_sub_one_ne_zero p n) hx).le
  have hcont : Continuous χ' := by
    refine continuous_iff_continuousAt.mpr fun g₀ => Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    obtain ⟨ζ, hζ⟩ := exists_primitive Ω p k
    haveI : NeZero (p ^ p ^ k - 1) := ⟨pow_pow_sub_one_ne_zero p k⟩
    have hV : IsOpen {g : A.decompositionSubgroup F | (g : Ω ≃ₐ[F] Ω) ζ = (g₀ : Ω ≃ₐ[F] Ω) ζ} :=
      (isOpen_setOf_apply (F := F) ζ (· = (g₀ : Ω ≃ₐ[F] Ω) ζ)).preimage continuous_subtype_val
    filter_upwards [hV.mem_nhds rfl] with g hg
    have hg' : (g : Ω ≃ₐ[F] Ω) ζ = (g₀ : Ω ≃ₐ[F] Ω) ζ := hg
    have he : PowOn p (g : Ω ≃ₐ[F] Ω) k (E g₀ k) := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
      rw [map_pow, hg', ← map_pow]; exact hE g₀ k _ hx
    have h1 : PadicInt.toZModPow k (χ' g - χ' g₀) = 0 := by
      rw [map_sub, key g k _ he, hχ' g₀ k, sub_self]
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h1
    rw [dist_eq_norm]; exact lt_of_le_of_lt h1 hk
  obtain ⟨σ, hσA, q, hq1, hσ⟩ := exists_frob_ne_one (F := F) A hp
  let σ' : A.decompositionSubgroup F := ⟨σ, hσA⟩
  have hne : χ' σ' ≠ 0 := by
    intro h0
    obtain ⟨ζ, hζ⟩ := exists_primitive Ω p (q + 1)
    have hq : q + 3 ≤ p ^ p ^ (q + 1) := by
      have h1 : q + 1 < p ^ (q + 1) := Nat.lt_pow_self hpp.one_lt
      have h2 : p ^ (q + 1) < p ^ p ^ (q + 1) := Nat.pow_lt_pow_right hpp.one_lt h1
      omega
    have hk := key σ' (q + 1) _ (hE σ' (q + 1))
    rw [h0, map_zero, eq_comm, ZMod.natCast_eq_zero_iff] at hk
    obtain ⟨j, hj⟩ := hk
    have hz1 : ζ ^ p ^ p ^ (q + 1) = ζ := by
      rw [← Nat.sub_add_cancel (one_lt_pow_pow p (q + 1)).le, pow_succ, hζ.pow_eq_one, one_mul]
    have hfix : ∀ j : ℕ, ζ ^ p ^ (p ^ (q + 1) * j) = ζ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz1]
    have hσζ : σ ζ = ζ := by
      have := hE σ' (q + 1) ζ hζ.pow_eq_one
      rw [hj, hfix] at this; exact this
    have hζq : ζ = ζ ^ q := by
      refine eq_of_pow_eq_one A (not_valuation_lt_one A hp (q + 1)) hζ.pow_eq_one
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) ?_
      have := hσ ζ (valuation_eq_one_of_pow_eq_one A (pow_pow_sub_one_ne_zero p (q + 1))
        hζ.pow_eq_one).le
      rwa [hσζ] at this
    have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (pow_pow_sub_one_ne_zero p (q + 1))
    have := hfin.pow_eq_pow_iff_modEq.1 (show ζ ^ 1 = ζ ^ q by rw [pow_one]; exact hζq)
    rw [← hζ.eq_orderOf] at this
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact hq1 this.symm
  obtain ⟨ψ, hψc, hψa, hψ0, hψ1⟩ := exists_normalized p χ' hcont hadd σ' hne
  exact ⟨ψ, hψc, hψa, fun g hg => hψ0 g (hine g hg), hψ1⟩

end main

theorem unrDec : ReciprocityTheory.ChartRestriction.T2.UnrDec := by
  intro F Ω _ _ _ _ _ p _ A hp
  exact main A hp

end GlobalTheory.UnrChar
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_padic_decomposition_hom_exists : ReciprocityTheory.ChartRestriction.T2.UnrDec := by
  atlas_forward_decl GlobalTheory.UnrChar.unrDec
end

section
section
noncomputable section

namespace GlobalTheory.PadicTop

open IsLocalRing Topology
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop TopEx)

theorem padicCoeff_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [TopologicalSpace O]
    [IsModuleTopology ℤ_[p] O] (hinj : Function.Injective (algebraMap ℤ_[p] O)) : PadicCoeff p O := by
  haveI : Module.IsTorsionFree ℤ_[p] O := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Free ℤ_[p] O := inferInstance
  haveI hR : IsTopologicalRing O := IsModuleTopology.isTopologicalRing ℤ_[p] O
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set b := Module.Free.chooseBasis ℤ_[p] O
  set e : O ≃ₗ[ℤ_[p]] (Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) := b.equivFun with he_def
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : O ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hp0 : (p : O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[p] O), Ne, ← map_zero (algebraMap ℤ_[p] O), hinj.eq_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpm : (p : O) ∈ maximalIdeal O := by
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[p]) (maximalIdeal O)
    have hc : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
      IsLocalRing.eq_maximalIdeal hmax
    rw [← map_natCast (algebraMap ℤ_[p] O), ← Ideal.mem_comap, hc, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have key1 : ∀ (n : ℕ) (x : O), ‖e x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → x ∈ Ideal.span {(p : O) ^ n} := by
    intro n x hx
    have hc : ∀ i, e x i ∈ Ideal.span {(p : ℤ_[p]) ^ n} := fun i =>
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 ((norm_le_pi_norm (e x) i).trans hx)
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hc i)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ i, c i • b i, ?_⟩
    have hx' : x = ∑ i, e x i • b i := (b.sum_equivFun x).symm
    conv_rhs => rw [hx']
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i]
    simp only [Algebra.smul_def, map_mul, map_pow, map_natCast]
    ring
  have key2 : ∀ (n : ℕ) (x : O), x ∈ Ideal.span {(p : O) ^ n} → ‖e x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    intro n x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have hy : y * (p : O) ^ n = ((p : ℤ_[p]) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    refine (pi_norm_le_iff_of_nonneg (zpow_pos hpR _).le).2 fun i => ?_
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, hy, map_smul, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton'.2 ⟨e y i, mul_comm _ _⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hsub1 : ∀ n : ℕ, Ideal.span {(p : O) ^ n} ≤ maximalIdeal O ^ n := fun n =>
    Ideal.span_le.2 (Set.singleton_subset_iff.2 (Ideal.pow_mem_pow hpm n))
  have hsub2 : ∀ n : ℕ, maximalIdeal O ^ (k * n) ≤ Ideal.span {(p : O) ^ n} := by
    intro n
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    have hk : ϖ ^ k = ↑u⁻¹ * (p : O) := by rw [hu, Units.inv_mul_cancel_left]
    rw [pow_mul, hk, mul_pow]
    exact Dvd.intro_left _ rfl
  refine ⟨hR, h.symm.compactSpace, h.symm.t2Space, ?_, hpm, hp0⟩
  refine isAdic_iff.2 ⟨fun n => ?_, fun s hs => ?_⟩
  · have hn : e ⁻¹' Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) ∈ 𝓝 (0 : O) :=
      he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact Metric.closedBall_mem_nhds 0 (zpow_pos hpR _))
    refine AddSubgroup.isOpen_of_mem_nhds (maximalIdeal O ^ n).toAddSubgroup (g := 0)
      (Filter.mem_of_superset hn fun x hx => hsub1 n (key1 n x ?_))
    simpa using hx
  · have ht : e.symm ⁻¹' s ∈ 𝓝 (0 : Module.Free.ChooseBasisIndex ℤ_[p] O → ℤ_[p]) :=
      he'.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hs)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
    refine ⟨k * n, fun x hx => ?_⟩
    have h1 := key2 n x (hsub2 n hx)
    have h2 : e x ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right]
      refine lt_of_le_of_lt h1 ?_
      rwa [zpow_neg, zpow_natCast, ← inv_pow]
    have := hball h2
    simpa using this

section FracTopology

variable {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']

def fracB (ϖ : O') (i : ℕ) : Submodule O' (FractionRing O') :=
  Submodule.span O' {algebraMap O' (FractionRing O') (ϖ ^ i)}

theorem mem_fracB {ϖ : O'} {i : ℕ} {x : FractionRing O'} :
    x ∈ fracB ϖ i ↔ ∃ c : O', x = algebraMap O' (FractionRing O') (c * ϖ ^ i) := by
  rw [fracB, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩

theorem algebraMap_mem_fracB {ϖ : O'} {i : ℕ} {x : O'} :
    algebraMap O' (FractionRing O') x ∈ fracB ϖ i ↔ ϖ ^ i ∣ x := by
  rw [mem_fracB]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [IsFractionRing.injective O' (FractionRing O') hc, mul_comm]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mul_comm]⟩

theorem fracB_anti (ϖ : O') {i j : ℕ} (h : i ≤ j) : fracB ϖ j ≤ fracB ϖ i := by
  rw [fracB, Submodule.span_singleton_le_iff_mem, algebraMap_mem_fracB]
  exact pow_dvd_pow ϖ h

theorem exists_pow_mul_mem {ϖ : O'} (hϖ : Irreducible ϖ) (a : FractionRing O') :
    ∃ n : ℕ, ∃ c : O', algebraMap O' (FractionRing O') (ϖ ^ n) * a =
      algebraMap O' (FractionRing O') c := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O') a
  have hs : (s : O') ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  refine ⟨n, ↑u⁻¹ * r, ?_⟩
  have hn : ϖ ^ n = ↑u⁻¹ * (s : O') := by rw [hu, Units.inv_mul_cancel_left]
  rw [hn, map_mul, map_mul, mul_assoc, mul_comm (algebraMap O' (FractionRing O') (s : O')) a]
  exact congrArg _ h

theorem fracB_basis {ϖ : O'} (hϖ : Irreducible ϖ) : SubmodulesRingBasis (fracB ϖ) where
  inter i j := ⟨max i j, le_inf (fracB_anti ϖ (le_max_left _ _)) (fracB_anti ϖ (le_max_right _ _))⟩
  leftMul a i := by
    obtain ⟨n, c, hc⟩ := exists_pow_mul_mem hϖ a
    refine ⟨i + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨d, rfl⟩ := mem_fracB.1 hx
    refine mem_fracB.2 ⟨c * d, ?_⟩
    have e : algebraMap O' (FractionRing O') (d * ϖ ^ (i + n)) =
        algebraMap O' (FractionRing O') (d * ϖ ^ i) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
      rw [← map_mul, pow_add, mul_assoc]
    show a * _ = _
    rw [e, mul_comm (algebraMap O' (FractionRing O') (d * ϖ ^ i)), ← mul_assoc, mul_comm a, hc,
      ← map_mul]
    congr 1
    ring
  mul i := ⟨i, by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_fracB.1 hx
    obtain ⟨d, rfl⟩ := mem_fracB.1 hy
    exact mem_fracB.2 ⟨c * d * ϖ ^ i, by show _ * _ = _; rw [← map_mul]; congr 1; ring⟩⟩

end FracTopology

theorem exists_fracTop (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [TopologicalSpace O'] (hA : IsAdic (IsLocalRing.maximalIdeal O')) :
    ∃ (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')), FracTop O' := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hm : ∀ n : ℕ, ((IsLocalRing.maximalIdeal O' ^ n : Ideal O') : Set O') = {x | ϖ ^ n ∣ x} := by
    intro n
    ext x
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      SetLike.mem_coe, Ideal.mem_span_singleton]
    rfl
  have hB := fracB_basis hϖ
  have hR := hB.toRing_subgroups_basis
  let τK : TopologicalSpace (FractionRing O') := hB.topology
  have hTR : IsTopologicalRing (FractionRing O') := hR.toRingFilterBasis.isTopologicalRing
  set f := algebraMap O' (FractionRing O') with hf
  have hnK := hR.hasBasis_nhds
  have hnO := hA.hasBasis_nhds
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    refine ((hnO x).tendsto_iff (hnK (f x))).2 fun i _ => ⟨i, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm] at hz
    show f (x + z) - f x ∈ fracB ϖ i
    rw [map_add, add_sub_cancel_left]
    exact algebraMap_mem_fracB.2 hz
  have hopen : IsOpenMap f := by
    refine IsOpenMap.of_nhds_le fun x => ?_
    refine Filter.le_map fun s hs => ?_
    obtain ⟨n, -, hn⟩ := (hnO x).mem_iff.1 hs
    refine Filter.mem_of_superset ((hnK (f x)).mem_of_mem (i := n) trivial) ?_
    intro b hb
    obtain ⟨c, hc⟩ := mem_fracB.1 (show b - f x ∈ fracB ϖ n from hb)
    refine ⟨x + c * ϖ ^ n, hn ⟨c * ϖ ^ n, ?_, rfl⟩, ?_⟩
    · rw [hm]
      exact Dvd.intro_left c rfl
    · rw [map_add, ← hc, add_sub_cancel]
  refine ⟨τK, inferInstance, continuousSMul_of_algebraMap O' (FractionRing O') hcont, ⟨?_⟩⟩
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
    (IsFractionRing.injective O' (FractionRing O')) hopen

theorem topEx : TopEx := by
  intro p _ O _ _ _ _ _ hinj
  letI τ : TopologicalSpace O := moduleTopology ℤ_[p] O
  haveI : IsModuleTopology ℤ_[p] O := ⟨rfl⟩
  have hO := padicCoeff_of_finite hinj
  obtain ⟨τK, h1, h2, h3⟩ := exists_fracTop O hO.adic
  exact ⟨τ, τK, h1, h2, hO, h3⟩

end GlobalTheory.PadicTop
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_finite_over_padic_topologies_exist : ReciprocityTheory.ChartRestriction.T2.TopEx := by
  atlas_forward_decl GlobalTheory.PadicTop.topEx
end

section
section
noncomputable section

open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT NumberField IsDedekindDomain ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.LocElem

theorem padicInt_coeff {p : ℕ} [Fact p.Prime] : PadicCoeff p ℤ_[p] := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [isAdic_iff]
    have key : ∀ n : ℕ, ((IsLocalRing.maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) := by
      intro n
      ext x
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, SetLike.mem_coe,
        ← PadicInt.norm_le_pow_iff_mem_span_pow, mem_closedBall_zero_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · rw [key]
      exact IsUltrametricDist.isOpen_closedBall _ (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne'
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (show (1:ℝ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt))
      refine ⟨n, ?_⟩
      rw [key]
      intro x hx
      apply hball
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_lt hx ?_
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact hn
  · rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem mulSub_open {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (hM : IsFGTop O M) (hO : PadicCoeff p O) {a : O} (ha : a ≠ 0) :
    IsOpen ((mulSub a M : Submodule O M) : Set M) := by
  have := hO.compact
  have := hO.ring
  have := hM.t2
  have := hM.csmul
  obtain ⟨s, hs⟩ := hM.fg.fg_top

  let f : (s → O) →ₗ[O] M := Fintype.linearCombination O (fun i : s => (i : M))
  have hfc : Continuous f := by
    show Continuous fun v : s → O => ∑ i, v i • (i : M)
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOf_mem, hs]
  have hq : Topology.IsQuotientMap f :=
    (hfc.isClosedMap).isQuotientMap hfc hfs

  have haO : IsOpen ((Ideal.span {a} : Ideal O) : Set O) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have e : (Ideal.span {(u : O) * ϖ ^ n} : Ideal O) = IsLocalRing.maximalIdeal O ^ n := by
      rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
        hϖ.maximalIdeal_eq]
    rw [e]
    exact (isAdic_iff.1 hO.adic).1 n
  have hopen : IsOpen ((((mulSub a M).comap f).toAddSubgroup : AddSubgroup (s → O)) : Set (s → O)) := by
    refine AddSubgroup.isOpen_mono (H₁ := (Submodule.pi Set.univ fun _ => (Ideal.span {a} : Ideal O)).toAddSubgroup) ?_ ?_
    · intro v hv
      have : ∀ i, ∃ w : O, a * w = v i := fun i => by
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hv i (Set.mem_univ i))
        exact ⟨w, by rw [mul_comm]; exact hw⟩
      choose w hw using this
      refine ⟨f w, ?_⟩
      show a • f w = f v
      rw [← map_smul]
      congr 1
      funext i
      exact hw i
    · show IsOpen (Set.univ.pi fun _ => ((Ideal.span {a} : Ideal O) : Set O))
      exact isOpen_set_pi Set.finite_univ fun _ _ => haO
  rw [← hq.isOpen_preimage]
  exact hopen

theorem contAction_quotient {O G V : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup V] [Module O V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : Representation O G V} (h : ReciprocityTheory.Gal.ContAction ρ)
    (T : Submodule O V) (hT : StableUnder ρ T) : ReciprocityTheory.Gal.ContAction (ρ.quotient T hT) := by
  have hq : IsOpenQuotientMap (Prod.map (id : G → G) T.mkQ) :=
    IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ T)
  unfold ReciprocityTheory.Gal.ContAction
  rw [hq.isQuotientMap.continuous_iff]
  exact continuous_quot_mk.comp h

theorem cup_eq_zero_of_coboundary {O : Type} [CommRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M T₂ P : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [AddCommGroup T₂] [Module O T₂] [TopologicalSpace T₂]
    [IsTopologicalAddGroup T₂] [ContinuousConstSMul O T₂] [AddCommGroup P] [Module O P]
    [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul O P]
    (ρM : Representation O Γ M) (ρ₂ : Representation O Γ T₂) (ρP : Representation O Γ P)
    (b : M →ₗ[O] T₂ →ₗ[O] P) (hb : Continuous fun q : M × T₂ => b q.1 q.2)
    (hbe : ∀ g x y, b (ρM g x) (ρ₂ g y) = ρP g (b x y)) (h₂ : ReciprocityTheory.Gal.ContAction ρ₂)
    (x : Z1 ρM) (t : Z1 ρ₂) (c : Γ → P) (hc : Continuous c)
    (hcz : ∀ g h, b (ρM g (x.1 h)) (t.1 g) = ρP g (c h) - c (g * h) + c g) :
    cupProductH1H1 ρM ρ₂ ρP b hb hbe h₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show (Submodule.Quotient.mk (cupCocycleZ1Z1 ρM ρ₂ ρP b hb hbe h₂ x t) : H2 ρP) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -(b (x.1 g) (t.1 g)) - c g, ((hb.comp (x.2.1.prodMk t.2.1)).neg).sub hc, ?_⟩
  funext q
  obtain ⟨g, h⟩ := q
  have e := hcz g h
  simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, map_sub, map_neg, ← hbe, x.2.2 g h, t.2.2 g h, map_add,
    LinearMap.add_apply]
  have e' : ρP g (c h) = b (ρM g (x.1 h)) (t.1 g) + c (g * h) - c g := by rw [e]; abel
  rw [e']
  abel

theorem pr_eq_zero_of_coboundary {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (x : Z1 D.ρA) (t : Z1 D.ρTl') (c : G → KO O) (hc : Continuous c)
    (hcz : ∀ g k, pairKO D.bT D.T (D.ρA g (x.1 k)) (t.1 g) = ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    D.pr (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show D.inv (cupProductH1H1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') (Submodule.Quotient.mk x) (Submodule.Quotient.mk t)) = 0
  have h0 := cup_eq_zero_of_coboundary D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') x t c hc (fun g k => hcz g k)
  exact (congrArg D.inv h0).trans (map_zero _)

theorem quotShape_of_equiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X]
    [Module O X] (Hc F Hc' F' : Submodule O X) (d : ℕ)
    (e : (Hc ⧸ F.comap Hc.subtype) ≃ₗ[O] (Hc' ⧸ F'.comap Hc'.subtype)) (h : QuotShape Hc F d) :
    QuotShape Hc' F' d := by
  obtain ⟨Cy, i1, i2, ι, π, hι, hex, c0, hc0⟩ := h
  refine ⟨Cy, i1, i2, e.toLinearMap ∘ₗ ι, π ∘ₗ e.symm.toLinearMap, e.injective.comp hι, ?_, c0, hc0⟩
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_range]
  rw [hex (e.symm y)]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [hz, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [← hz, LinearEquiv.symm_apply_apply]⟩

theorem mem_integers_iff_norm_le_one {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 :=
  GlobalTheory.EmbInj.mem_OL_iff LL x

theorem isOpen_integers {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) :
    IsOpen (Set.range (algebraMap ↥(Formalism.BasicNotions.Loc.OL LL) ↥LL.1)) :=
  (GlobalTheory.LitGood.litGoodO l LL).2.2.2.2

theorem elem : ReciprocityTheory.ChartRestriction.T2.Elem where
  padicInt := padicInt_coeff
  mulSub := @fun _ _ _ _ _ _ _ _ _ _ _ hM hO _ ha => mulSub_open hM hO ha
  contQuot := fun h T hT => contAction_quotient h T hT
  swapCob := fun D x t c hc hcz => pr_eq_zero_of_coboundary D x t c hc hcz
  shapeEquiv := fun Hc F Hc' F' d e h => quotShape_of_equiv Hc F Hc' F' d e h
  memOL := fun LL x => mem_integers_iff_norm_le_one LL x
  openOL := fun LL => isOpen_integers LL

end GlobalTheory.LocElem
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_cohomology_seven_elementary_facts : ReciprocityTheory.ChartRestriction.T2.Elem := by
  atlas_forward_decl GlobalTheory.LocElem.elem
end

section
section
namespace GlobalTheory

theorem langRecCore_of_artinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hT : Formalism.GaloisCohomology.LocalTateDualityK)
    (hE : Formalism.GaloisCohomology.LocalEulerCharK) : ReciprocityTheory.ChartRestriction.T2.Core where
  dec := GlobalTheory.T.decomposition_group_equiv_local_galois_group
  inv := GlobalTheory.T.invIso_of_localTateDuality hT
  fin := GlobalTheory.T.finIso_dualLattice_of_localTateDuality hT
  rat := GlobalTheory.T.rationalLocalDuality_of_localTateDuality hT
  int := GlobalTheory.T.integral_localDuality_of_localTateDuality hT
  jspan := GlobalTheory.T.span_of_local_cohomology_shape
  nat := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT
  shape := GlobalTheory.T.cohomology_shape_of_tate_duality_euler hT hE
  shapeUnr := GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality hT hE
  unr := GlobalTheory.T.unramified_padic_decomposition_hom_exists
  vhE := GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA
  top := GlobalTheory.T.dvr_finite_over_padic_topologies_exist
  elem := GlobalTheory.T.local_cohomology_seven_elementary_facts

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.Core := by
  atlas_forward_decl GlobalTheory.langRecCore_of_artinReciprocity
end

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.FinInvKO

theorem isFiniteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem length_lt_top_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : Submodule O (KmodO O)) {c : O} (hc : c ≠ 0) (h : ∀ x ∈ S, c • x = 0) :
    Module.length O S < ⊤ := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (FractionRing O)).ne hc
  let x₀ : KmodO O := Submodule.Quotient.mk ((algebraMap O (FractionRing O) c)⁻¹)
  let ψ : O →ₗ[O] KmodO O := LinearMap.toSpanSingleton O _ x₀
  have hS : S ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 := h _ hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : algebraMap O (FractionRing O) a = algebraMap O (FractionRing O) c * y := by
      rw [← Algebra.smul_def]; exact ha
    refine ⟨a, ?_⟩
    simp only [ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ha', mul_comm (algebraMap O (FractionRing O) c) y, mul_assoc,
      mul_inv_cancel₀ hc', mul_one]
  have hk : ∀ z : LinearMap.range ψ, c • z = 0 := by
    rintro ⟨_, a, rfl⟩
    ext1
    simp only [SetLike.val_smul, ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul,
      smul_smul, Submodule.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a, ?_⟩
    rw [Algebra.linearMap_apply, Algebra.smul_def, map_mul, mul_comm (algebraMap O (FractionRing O) c), mul_assoc, mul_inv_cancel₀ hc', mul_one]
  have hfl := isFiniteLength_of_killed hc hk
  exact lt_of_le_of_lt (Module.length_le_of_injective (Submodule.inclusion hS) (Submodule.inclusion_injective hS))
    (lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 hfl))

theorem finiteLength_invariants_negTwist_KmodO : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants
      ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤ := by
  intro D i w hw e he
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := hgI.1
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  haveI : CharZero (FractionRing (D.nd.O i)) :=
    (D.nd.embK i).charZero_iff (D.nd.embK i).injective |>.1 inferInstance
  haveI : CharZero (D.nd.O i) := (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).charZero
  have hle : 1 ≤ (1 + D.nd.l i ^ D.nd.s0 i) ^ e := Nat.one_le_pow _ _ (by omega)
  have hlt : 1 < (1 + D.nd.l i ^ D.nd.s0 i) ^ e :=
    Nat.one_lt_pow he.ne' (by have := pow_pos hp.pos (D.nd.s0 i); omega)
  have hc : (((1 + D.nd.l i ^ D.nd.s0 i) ^ e - 1 : ℕ) : D.nd.O i) ≠ 0 :=
    Nat.cast_ne_zero.2 (by omega)
  refine length_lt_top_of_killed _ hc fun v hv => ?_
  have h1 := hv ⟨g, hgD⟩
  change ((((Glob.epsO D.nd i) ^ (-(e : ℤ))) g : (D.nd.O i)ˣ) : D.nd.O i) • v = v at h1
  have hu : ((Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) = 1 + (D.nd.l i : D.nd.O i) ^ D.nd.s0 i := by
    simp [Glob.epsO, hg]
  have h2 : (((Glob.epsO D.nd i g) ^ e : (D.nd.O i)ˣ) : D.nd.O i) • v = v := by
    conv_lhs => rw [← h1]
    rw [smul_smul, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel,
      zpow_zero, Units.val_one, one_smul]
  rw [Nat.cast_sub hle, Nat.cast_one, sub_smul, one_smul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h2, sub_self]

end GlobalTheory.FinInvKO
end
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.SelmerBoundAtPoint

theorem finCore : Formalism.MainNotions.N.K.H0.FinCore :=
  ⟨fun {D} i r ρ π g2 w hw => GlobalTheory.FiniteTwistInvariants.main D i r ρ π g2 w hw,
   fun {D} i w hw e he => GlobalTheory.FinInvKO.finiteLength_invariants_negTwist_KmodO D i w hw e he⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hA hT hE D i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin tie a51 unr hR hL hTB
  have : Fact ReciprocityTheory.ChartRestriction.T2.Core := ⟨GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler hA hT hE⟩
  have : Fact Formalism.MainNotions.N.K.H0.FinCore := ⟨finCore⟩
  exact Formalism.MainNotions.N.K.Closed.theorem_n5_from_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin
    tie a51 (Formalism.MainNotions.N.K.StD.unramified_input_of_admitted i dc unr) hR hL hTB

end GlobalTheory.SelmerBoundAtPoint
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  atlas_forward_decl GlobalTheory.SelmerBoundAtPoint.main
end
