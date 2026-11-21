import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Klen

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.kexp :
    ∀ (CK eps c0 x : ℝ) (e n n0 D : ℕ), 0 < CK → 0 < eps → 0 ≤ c0 → 1 ≤ x → (e : ℝ) ≤ x ^ (eps / (2 * CK)) → n ≤ n0 →
      Real.log (2 * (D : ℝ)) ≤ c0 * x ^ (eps / 4) →
        kBound CK e n D ≤ Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by
  intro CK eps c0 x e n n0 D hCK heps hc0 hx he hn hD
  have hx0 : 0 < x := by linarith
  have hn' : (n : ℝ) ≤ n0 := by exact_mod_cast hn
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn00 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have hy : 0 ≤ x ^ (eps / (2 * CK)) := Real.rpow_nonneg hx0.le _
  have h1 : 2 * (e : ℝ) * n ≤ (2 * (n0 : ℝ)) * x ^ (eps / (2 * CK)) := by
    have := mul_le_mul he hn' hn0 hy
    nlinarith
  have h2 : (2 * (e : ℝ) * n) ^ CK ≤ (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
    calc (2 * (e : ℝ) * n) ^ CK ≤ ((2 * (n0 : ℝ)) * x ^ (eps / (2 * CK))) ^ CK :=
          Real.rpow_le_rpow (by positivity) h1 hCK.le
      _ = (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
          rw [Real.mul_rpow (by positivity) hy, ← Real.rpow_mul hx0.le]
          congr 2
          field_simp
  have h3 : x ^ (3 * eps / 4) = x ^ (eps / 2) * x ^ (eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  unfold kBound
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ (2 * (e : ℝ) * n) ^ CK := Real.rpow_nonneg (by positivity) _
  have hb : 0 ≤ c0 * x ^ (eps / 4) := mul_nonneg hc0 (Real.rpow_nonneg hx0.le _)
  calc (2 * (e : ℝ) * n) ^ CK * Real.log (2 * (D : ℝ))
      ≤ (2 * (e : ℝ) * n) ^ CK * (c0 * x ^ (eps / 4)) := mul_le_mul_of_nonneg_left hD ha
    _ ≤ ((2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2)) * (c0 * x ^ (eps / 4)) := mul_le_mul_of_nonneg_right h2 hb
    _ = (2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4) := by rw [h3]; ring
end

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.point :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R c : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀], HasMuQ l L₀ → SecondBound l R L₀ →
      ∀ (Z : ℕ) (Exc : Finset ℕ), FirstBound l R c L₀ Z Exc →
        ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂], IsLayer l (jZero l R) L₀ L₂ →
          ∀ (eps Ct c0 x : ℝ) (n0 : ℕ), 0 < eps → 0 ≤ c0 → 1 ≤ x → Good (eps / (2 * CK)) Ct Exc x →
            Module.finrank ℚ L₂ ≤ n0 → Real.log (2 * ((discr L₂).natAbs : ℝ)) ≤ c0 * x ^ (eps / 4) →
            ∀ e : ℕ, 1 ≤ e → e ≤ Z → (e : ℝ) ≤ x ^ Ct →
              ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
                shaInv L₁ l e ≠ ⊤ ∧ ((shaInv L₁ l e).toNat : ℝ) ≤
                  (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) +
                    2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by
  intro CK hCK hK l R c _ L₀ _ hmu hSec Z Exc hF L₂ _ _ _ hL₂ eps Ct c0 x n0 heps hc0 hx hgood hn hdisc e he1 heZ hex m L₁ _ _ _ hL₁
  have hexp : 0 ≤ 2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by positivity
  by_cases he : e ∈ Exc
  · have hg : (e : ℝ) ≤ x ^ (eps / (2 * CK)) := hgood e he hex
    obtain ⟨D⟩ := ldata_nonempty (F := L₂) (Ω := AlgebraicClosure L₂) l
    have hmu2 : HasMuQ l L₂ := by
      obtain ⟨ζ, hζ⟩ := hmu
      exact ⟨algebraMap L₀ L₂ ζ, hζ.map_of_injective (algebraMap L₀ L₂).injective⟩
    obtain ⟨hvt, hvb⟩ := klen CK hK l L₂ (AlgebraicClosure L₂) D hmu2 e he1
    have hkb := kexp CK eps c0 x e (Module.finrank ℚ L₂) n0 (discr L₂).natAbs hCK heps hc0 hx hg hn hdisc
    have hs := hSec e he1 m L₁ hL₁ L₂ hL₂ (AlgebraicClosure L₂) D
    generalize VLen D ↑e = v at hvt hvb hs
    generalize shaInv L₁ l ↑e = s at hs ⊢
    lift v to ℕ using hvt
    have hst : s ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ hs
      rw [← Nat.cast_add]
      exact ENat.coe_ne_top _
    lift s to ℕ using hst
    have hs' : s ≤ v + R * (m - jZero l R) := by exact_mod_cast hs
    refine ⟨ENat.coe_ne_top s, ?_⟩
    rw [ENat.toNat_coe]
    simp only [ENat.toNat_coe] at hvb
    have hN : s ≤ v + R * (m + jZero l R + c + Nat.log l Z) := by
      refine le_trans hs' (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
      omega
    have hR : (s : ℝ) ≤ (v : ℝ) + (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) := by
      exact_mod_cast hN
    linarith
  · have hb := hF.2 e he1 heZ he m L₁ hL₁
    generalize shaInv L₁ l ↑e = s at hb ⊢
    have hst : s ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hb
    lift s to ℕ using hst
    have hs' : s ≤ R * (max m (jZero l R) + c + Nat.log l Z) := by exact_mod_cast hb
    refine ⟨ENat.coe_ne_top s, ?_⟩
    rw [ENat.toNat_coe]
    have hN : s ≤ R * (m + jZero l R + c + Nat.log l Z) := by
      refine le_trans hs' (Nat.mul_le_mul_left _ ?_)
      omega
    have hR : (s : ℝ) ≤ (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) := by
      exact_mod_cast hN
    linarith
end

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.logs :
    (∀ (l : ℕ) (J Ct X x : ℝ), 2 ≤ l → 0 < J → 0 ≤ Ct → 1 ≤ X → X ^ (1 / J) ≤ x →
        ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * Ct * J * Real.log x) ∧
      (∀ (J eps X x : ℝ), 0 < J → 0 < eps → 1 ≤ X → X ^ (1 / J) ≤ x → X ^ (eps / (4 * J)) ≤ x ^ (eps / 4)) ∧
      (∀ (e : ℕ) (A1 x : ℝ), 1 ≤ x → (2 : ℝ) ^ e ≤ x ^ A1 → (e : ℝ) + 2 ≤ (2 * |A1| + 2) * (1 + Real.log x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l J Ct X x hl hJ hCt hX hx
    have hX0 : 0 < X := by linarith
    have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hX (by positivity)) hx
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogX : Real.log X ≤ J * Real.log x := by
      have h1 : Real.log (X ^ (1 / J)) ≤ Real.log x :=
        Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hx
      rw [Real.log_rpow hX0] at h1
      have h2 : J * ((1 / J) * Real.log X) = Real.log X := by field_simp
      calc Real.log X = J * ((1 / J) * Real.log X) := h2.symm
        _ ≤ J * Real.log x := mul_le_mul_of_nonneg_left h1 hJ.le
    have hl2 : (1:ℝ) / 2 < Real.log l := by
      have h3 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) (by exact_mod_cast hl)
      have h4 := Real.log_two_gt_d9
      linarith
    rcases Nat.eq_zero_or_pos ⌊X ^ Ct⌋₊ with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCt) hJ.le) hlogx
    · have hpow : (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ X ^ Ct := by
        have h1 : l ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ ⌊X ^ Ct⌋₊ := Nat.pow_log_le_self l hpos.ne'
        have h2 : ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ X ^ Ct := Nat.floor_le (Real.rpow_nonneg hX0.le _)
        calc (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) = ((l ^ (Nat.log l ⌊X ^ Ct⌋₊) : ℕ) : ℝ) :=
              (Nat.cast_pow l _).symm
          _ ≤ ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ X ^ Ct := h2
      have hl0 : (0:ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have hlog := Real.log_le_log (pow_pos hl0 _) hpow
      rw [Real.log_pow, Real.log_rpow hX0] at hlog
      have hk0 : (0:ℝ) ≤ (Nat.log l ⌊X ^ Ct⌋₊ : ℕ) := Nat.cast_nonneg _
      have hk : ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * (((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) * Real.log l) := by
        nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0]
      nlinarith [mul_le_mul_of_nonneg_left hlogX hCt]
  · intro J eps X x hJ heps hX hx
    have hX0 : 0 ≤ X := by linarith
    have h1 : X ^ (eps / (4 * J)) = (X ^ (1 / J)) ^ (eps / 4) := by
      rw [← Real.rpow_mul hX0]
      congr 1
      field_simp
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hx (by positivity)
  · intro e A1 x hx h
    have hx0 : 0 < x := by linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_rpow hx0] at hlog
    have h2 := Real.log_two_gt_d9
    have habs : A1 * Real.log x ≤ |A1| * Real.log x :=
      mul_le_mul_of_nonneg_right (le_abs_self A1) hlogx
    have he0 : (0:ℝ) ≤ e := Nat.cast_nonneg e
    have he : (e:ℝ) ≤ 2 * (e * Real.log 2) := by nlinarith
    nlinarith [abs_nonneg A1, mul_nonneg (abs_nonneg A1) hlogx]
end

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.point2 :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R c1 n0 : ℕ) [Fact l.Prime] (c0 J Ct eps a : ℝ), 0 ≤ c0 → 0 < J → 0 ≤ Ct → 0 < eps →
      0 ≤ a → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀], HasMuQ l L₀ → SecondBound l R L₀ →
        ∀ (c : ℕ) (X : ℝ) (Exc : Finset ℕ), c ≤ c1 → FirstBound l R c L₀ ⌊X ^ Ct⌋₊ Exc →
        ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂], IsLayer l (jZero l R) L₀ L₂ → Module.finrank ℚ L₂ ≤ n0 →
          ∀ x : ℝ, 1 ≤ x → X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
            Real.log (2 * ((discr L₂).natAbs : ℝ)) ≤ c0 * x ^ (eps / 4) →
            ∀ e : ℕ, 1 ≤ e → (e : ℝ) ≤ x ^ Ct →
              ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
                (m : ℝ) ≤ a * (1 + Real.log x) →
                  shaInv L₁ l e ≠ ⊤ ∧ ((shaInv L₁ l e).toNat : ℝ) + 1 ≤ ptBound C eps x := by
  intro CK hCK hK l R c1 n0 hl c0 J Ct eps a hc0 hJ hCt heps ha
  have hA : 0 ≤ (R : ℝ) * (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) + 1 := by positivity
  have hB : 0 ≤ (2 * (n0 : ℝ)) ^ CK * c0 := by positivity
  refine ⟨((R : ℝ) * (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) + 1) + (2 * (n0 : ℝ)) ^ CK * c0, by positivity, ?_⟩
  intro L₀ _ hmu hS c X Exc hc hF L₂ _ _ _ hL₂ hn x hx hXx hxX hG hD e he hex m L₁ _ _ _ hL₁ hm
  have hX : 1 ≤ X := hx.trans hxX
  have heZ : e ≤ ⌊X ^ Ct⌋₊ :=
    Nat.le_floor (hex.trans (Real.rpow_le_rpow (by linarith) hxX hCt))
  obtain ⟨h1, h2⟩ := UpperTheory.V.Win.point CK hCK hK l R c L₀ hmu hS _ Exc hF L₂ hL₂ eps Ct c0 x n0 heps hc0 hx hG hn hD
    e he heZ hex m L₁ hL₁
  refine ⟨h1, ?_⟩
  have hlog := UpperTheory.V.Win.logs.1 l J Ct X x hl.out.two_le hJ hCt hX hXx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hcr : (c : ℝ) ≤ c1 := by exact_mod_cast hc
  have hp : 0 ≤ x ^ (3 * eps / 4) := by positivity
  have hj : (0 : ℝ) ≤ jZero l R := Nat.cast_nonneg _
  have hc1 : (0 : ℝ) ≤ c1 := Nat.cast_nonneg _
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hCJ : 0 ≤ 2 * Ct * J := by positivity
  have hin : (m : ℝ) + jZero l R + c + Nat.log l ⌊X ^ Ct⌋₊ ≤
      (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) * (1 + Real.log x) := by
    nlinarith [mul_nonneg hj hL, mul_nonneg hc1 hL]
  have hR' := mul_le_mul_of_nonneg_left hin hR
  have hexp : Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) ≤
      Real.exp ((((R : ℝ) * (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) + 1) + (2 * (n0 : ℝ)) ^ CK * c0) *
        x ^ (3 * eps / 4)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) hp
  unfold ptBound
  have hBL : 0 ≤ (2 * (n0 : ℝ)) ^ CK * c0 * (1 + Real.log x) := by positivity
  nlinarith
end
