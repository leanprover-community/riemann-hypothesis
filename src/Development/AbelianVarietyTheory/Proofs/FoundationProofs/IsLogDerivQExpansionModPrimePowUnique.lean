import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGaussStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponentsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConstStatement

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem primCan_mul_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (c : Ω) (a b : HahnSeries ℚ Ω)
    (ha : ∀ r, a.coeff r ∈ A) (hb : ∀ r, ∃ z ∈ A, b.coeff r = c * z) :
    ∀ r, ∃ z ∈ A, (a * b).coeff r = c * z := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = c * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, A.add_mem _ _ hz hw, by ring⟩
  · exact ⟨0, A.zero_mem, by simp⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hb ij.2
    exact ⟨a.coeff ij.1 * z, A.mul_mem _ _ (ha _) hz, by rw [e]; ring⟩

theorem primCan : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P →
    (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) →
    (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  intro Ω _ _ _ l _ A hl n L P φ hL hP hden hφ hφP
  obtain ⟨Q, hQ, -, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L P hL hP hden
  have h1 : ∀ r, ∃ z ∈ A, (Q * P - 1).coeff r = (l : Ω) ^ n * z := by
    intro r
    obtain ⟨z, hz, e⟩ := hQP r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub]; exact e⟩
  have h2 := primCan_mul_dvd A _ φ _ hφ h1
  have h3 : ∀ r, ∃ z ∈ A, (Q * (φ * P)).coeff r = (l : Ω) ^ n * z := by
    refine primCan_mul_dvd A _ Q _ hQ ?_
    intro r
    obtain ⟨z, hz, e⟩ := hφP r
    exact ⟨z, hz, by rw [← e, sub_zero]⟩
  intro r
  obtain ⟨z, hz, ez⟩ := h3 r
  obtain ⟨w, hw, ew⟩ := h2 r
  have hid : φ = Q * (φ * P) - φ * (Q * P - 1) := by ring
  refine ⟨z - w, sub_mem hz hw, ?_⟩
  rw [sub_zero, hid, HahnSeries.coeff_sub, ez, ew]
  ring

end GlobalTheory
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P → (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) → (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  first | exact @GlobalTheory.primCan | exact GlobalTheory.primCan | (intros; apply GlobalTheory.primCan <;> assumption)
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue.DlUniq

variable {Ω : Type} [Field Ω]

theorem cg_mul (A : ValuationSubring Ω) (l n : ℕ) (D G : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hG : ∀ r, G.coeff r ∈ A) : ∀ r, CgA A l n ((D * G).coeff r) 0 := by
  intro r
  have h : ∀ i, ∃ z ∈ A, D.coeff i = (l : Ω) ^ n * z := fun i => by
    obtain ⟨z, hz, e⟩ := hD i; exact ⟨z, hz, by simpa using e⟩
  choose z hzA hz using h
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support G.isPWO_support r, z ij.1 * G.coeff ij.2, ?_, ?_⟩
  · exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hzA _) (hG _))
  · rw [HahnSeries.coeff_mul, sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    rw [hz, mul_assoc]

theorem cg_sub (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hE : ∀ r, CgA A l n (E.coeff r) 0) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  refine ⟨z - w, A.sub_mem hz hw, ?_⟩
  rw [HahnSeries.coeff_sub, sub_zero, mul_sub, ← e, ← e', sub_zero, sub_zero]

theorem cg_of (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (h : ∀ r, CgA A l n (D.coeff r) (E.coeff r)) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := h r
  exact ⟨z, hz, by rw [HahnSeries.coeff_sub, sub_zero, e]⟩

theorem key (θ : HahnSeries ℚ Ω → HahnSeries ℚ Ω)
    (hL : ∀ P Q, θ (P * Q) = θ P * Q + P * θ Q) (hC : ∀ c : Ω, θ (HahnSeries.C c) = 0)
    (k k2 : Ω) (hk : k ≠ 0) (a b a2 b2 : HahnSeries ℚ Ω)
    (h : HahnSeries.C k * a * b2 = HahnSeries.C k2 * a2 * b) :
    (θ a * b - a * θ b) * (a2 * b2) = (θ a2 * b2 - a2 * θ b2) * (a * b) := by
  have e1 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k * (θ a * b2 + a * θ b2) := by
    rw [mul_assoc, hL, hC, hL]; ring
  have e2 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k2 * (θ a2 * b + a2 * θ b) := by
    rw [h, mul_assoc, hL, hC, hL]; ring
  have h0 : HahnSeries.C k * ((θ a * b - a * θ b) * (a2 * b2) - (θ a2 * b2 - a2 * θ b2) * (a * b)) = 0 := by
    linear_combination (-(a2 * b)) * e1 + (a2 * b) * e2 - (θ a2 * b + a2 * θ b) * h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 (HahnSeries.C_ne_zero hk)
  · exact sub_eq_zero.mp h1

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue.DlUniq

theorem T_pow_mem_Gamma (M : ℕ) : (ModularGroup.T ^ M : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  have h := ModularGroup.coe_T_zpow (M : ℤ)
  rw [zpow_natCast] at h
  simp [h]

theorem mem_KT {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (f : X.K) :
    ∃ M : ℕ, 0 < M ∧ f ∈ KT X M := by
  obtain ⟨M, hM, h⟩ := X.level f
  exact ⟨M, hM, h _ (T_pow_mem_Gamma M)⟩

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue

open GlobalTheory.Glue.DlUniq in

theorem isDl_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), IsDl X A l n s f φ → IsDl X A l n s f φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X _ l _ A hl n s f φ φ' h1 h2
  obtain ⟨hφA, a, b, κ, hκ, hab, hPa, hPb, hφ⟩ := h1
  obtain ⟨hφ'A, a2, b2, κ2, hκ2, hab2, hPa2, hPb2, hφ'⟩ := h2
  have hth := fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q)

  have hK : algebraMap Ω X.K κ * a * b2 = algebraMap Ω X.K κ2 * a2 * b := by
    rw [← hab, ← hab2]; ring
  have hE : HahnSeries.C κ * X.exp a * X.exp b2 = HahnSeries.C κ2 * X.exp a2 * X.exp b := by
    have := congrArg X.exp hK
    simp only [map_mul, AlgHom.commutes] at this
    have ec : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.C c := fun c => by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]; simp [HahnSeries.ofPowerSeries_C]
    rwa [ec, ec] at this
  have hkey := key (theta s) (fun P Q => (hth P Q).1) (fun c => (hth 0 0).2.2 c) κ κ2 hκ _ _ _ _ hE

  set P := X.exp a * X.exp b * (X.exp a2 * X.exp b2) with hP
  have hPab := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa hPb
  have hPab2 := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa2 hPb2
  have hPP : Prim A P := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPab hPab2
  obtain ⟨M, hM, hMK⟩ := mem_KT X (a * b * (a2 * b2))
  have hsupp := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X M hM _).mp hMK
  have hsuppP : ∀ r : ℚ, P.coeff r ≠ 0 → (r * M).den = 1 := by
    simpa [hP, map_mul] using hsupp
  have hD1 := cg_mul A l n _ _ (cg_of A l n _ _ hφ) hPab2.1
  have hD2 := cg_mul A l n _ _ (cg_of A l n _ _ hφ') hPab.1
  have hdiff := cg_sub A l n _ _ hD1 hD2
  have hid : (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) * (X.exp a2 * X.exp b2) -
      (φ' * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) * (X.exp a * X.exp b)
      = (φ - φ') * P := by
    rw [hP]; linear_combination (-1 : HahnSeries ℚ Ω) * hkey
  rw [hid] at hdiff
  have hint : ∀ r, (φ - φ').coeff r ∈ A := fun r => by
    rw [HahnSeries.coeff_sub]; exact sub_mem (hφA r) (hφ'A r)
  have hfin := GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow l A hl n M P (φ - φ') hM hPP hsuppP hint hdiff
  intro r
  obtain ⟨z, hz, e⟩ := hfin r
  exact ⟨z, hz, by rw [← e, HahnSeries.coeff_sub, sub_zero]⟩

end GlobalTheory.Glue
end
