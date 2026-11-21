import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import BuildAid.ForwardExisting

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem frobenius_affine_integral (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S]
    [ValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] (d : ℕ)
    (U : Matrix (Fin d) (Fin d) S) (z : Fin d → S) (y : Fin d → K)
    (h : ∀ i, y i ^ p = (U.map (algebraMap S K) *ᵥ y) i + algebraMap S K (z i)) :
    ∀ i, y i ∈ (algebraMap S K).range := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set w := ValuationRing.valuation S K with hw
  have hint : ∀ s : S, w (algebraMap S K s) ≤ 1 := fun s =>
    (ValuationRing.mem_integer_iff S K _).2 ⟨s, rfl⟩
  intro i0
  have hi0 : Finset.univ.Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => w (y j)) hi0
  have hM : w (y i) ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hle : w (y i) ^ p ≤ w (y i) := by
      rw [← map_pow, h i]
      refine (Valuation.map_add_le w ?_ ?_)
      · simp only [Matrix.mulVec, dotProduct]
        refine Valuation.map_sum_le w fun j _ => ?_
        rw [map_mul, Matrix.map_apply]
        calc w (algebraMap S K (U i j)) * w (y j) ≤ 1 * w (y i) :=
              mul_le_mul' (hint _) (hmax j (Finset.mem_univ _))
          _ = w (y i) := one_mul _
      · exact (hint _).trans hgt.le
    have h2 : w (y i) ^ 2 ≤ w (y i) ^ p := pow_le_pow_right₀ hgt.le hp
    have h3 : w (y i) * w (y i) ≤ 1 * w (y i) := by
      rw [one_mul, ← sq]; exact h2.trans hle
    have h0 : 0 < w (y i) := lt_trans zero_lt_one hgt
    exact absurd (le_of_mul_le_mul_right h3 h0) (not_le.2 hgt)
  have : w (y i0) ≤ 1 := (hmax i0 (Finset.mem_univ _)).trans hM
  obtain ⟨s, hs⟩ := (ValuationRing.mem_integer_iff S K _).1 this
  exact ⟨s, hs⟩

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_schreier_system_integral : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] (d : ℕ) (U : Matrix (Fin d) (Fin d) S) (z : Fin d → S) (y : Fin d → K), (∀ i, y i ^ p = (U.map (algebraMap S K) *ᵥ y) i + algebraMap S K (z i)) → ∀ i, y i ∈ (algebraMap S K).range := by
  atlas_forward_decl GlobalTheory.frobenius_affine_integral
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

theorem map_frobenius_charP (p : ℕ) [Fact p.Prime] {S K : Type} [CommRing S] [CommRing K] [CharP S p] [CharP K p]
    (f : S →+* K) (x : WittVector p S) :
    WittVector.map f (WittVector.frobenius x) = WittVector.frobenius (WittVector.map f x) := by
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow]

theorem map_mulVec_witt (p : ℕ) [Fact p.Prime] {S K : Type} [CommRing S] [CommRing K] (f : S →+* K) (d : ℕ)
    (U : Matrix (Fin d) (Fin d) (WittVector p S)) (B : Fin d → WittVector p S) (i : Fin d) :
    WittVector.map f ((U *ᵥ B) i) = (U.map (WittVector.map f) *ᵥ (fun j => WittVector.map f (B j))) i := by
  rw [RingHom.map_mulVec]; rfl

theorem step : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Z : Fin d → WittVector p S) (Y : Fin d → WittVector p K), (∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i + WittVector.map (algebraMap S K) (Z i)) → ∃ (B Z₁ : Fin d → WittVector p S) (Y₁ : Fin d → WittVector p K), (∀ i, Y i = WittVector.map (algebraMap S K) (B i) + (p : WittVector p K) * Y₁ i) ∧ ∀ i, WittVector.frobenius (Y₁ i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y₁) i + WittVector.map (algebraMap S K) (Z₁ i) := by
  intro p _ S K _ _ _ _ _ _ _ _ _ _ d U Z Y hY
  set f : S →+* K := algebraMap S K with hf
  set F : WittVector p S →+* WittVector p K := WittVector.map f with hF

  have h0 : ∀ i, (Y i).coeff 0 ^ p = ((U.map WittVector.constantCoeff).map f *ᵥ fun j => (Y j).coeff 0) i
      + f ((Z i).coeff 0) := by
    intro i
    have := congrArg (fun w => w.coeff 0) (hY i)
    rw [WittVector.coeff_frobenius_charP] at this
    rw [this]
    have e1 := RingHom.map_mulVec (WittVector.constantCoeff (p := p) (R := K)) (U.map F) Y i
    change WittVector.constantCoeff ((U.map F *ᵥ Y) i + F (Z i)) = _
    rw [map_add, e1]
    simp [Matrix.map_map, Function.comp_def, WittVector.constantCoeff_apply, hF, WittVector.map_coeff]
  have hb : ∀ i, ∃ c, f c = (Y i).coeff 0 := fun i =>
    RingHom.mem_range.mp (GlobalTheory.T.artin_schreier_system_integral p S K d (U.map WittVector.constantCoeff) (fun i => (Z i).coeff 0)
      (fun i => (Y i).coeff 0) h0 i)
  choose b hbY using hb
  set B : Fin d → WittVector p S := fun i => WittVector.teichmuller p (b i) with hB
  have hdiff : ∀ i, ∃ c, Y i - F (B i) = (p : WittVector p K) * c := by
    intro i
    have hm : Y i - F (B i) ∈ Ideal.span {(p : WittVector p K)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, hB, hF, WittVector.map_teichmuller,
        WittVector.teichmuller_coeff_zero, hbY, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose Y₁ hY₁ using hdiff
  have hYfun : Y = (fun j => F (B j)) + (p : WittVector p K) • Y₁ := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hY₁ j
  set Wv : Fin d → WittVector p S := fun i => (U *ᵥ B) i + Z i - WittVector.frobenius (B i) with hWv
  have hWimg : ∀ i, F (Wv i) = (p : WittVector p K) * (WittVector.frobenius (Y₁ i) - (U.map F *ᵥ Y₁) i) := by
    intro i
    have h := hY i
    have e2 : (U.map F *ᵥ Y) i = (U.map F *ᵥ fun j => F (B j)) i + (p : WittVector p K) * (U.map F *ᵥ Y₁) i := by
      rw [hYfun, Matrix.mulVec_add, Matrix.mulVec_smul]
      rfl
    have e3 : Y i = F (B i) + (p : WittVector p K) * Y₁ i := by linear_combination hY₁ i
    rw [e2, e3, map_add, map_mul, map_natCast] at h
    have e4 : F (Wv i) = (U.map F *ᵥ fun j => F (B j)) i + F (Z i) - WittVector.frobenius (F (B i)) := by
      rw [hWv]
      simp only
      rw [map_sub, map_add, map_mulVec_witt, hF, map_frobenius_charP]
    rw [e4]
    linear_combination (-1 : WittVector p K) * h
  have hW0 : ∀ i, (Wv i).coeff 0 = 0 := by
    intro i
    apply IsFractionRing.injective S K
    rw [map_zero]
    have h1 : F (Wv i) ∈ Ideal.span {(p : WittVector p K)} :=
      Ideal.mem_span_singleton'.mpr ⟨_, by rw [hWimg i, mul_comm]⟩
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, hF, WittVector.map_coeff] at h1
    exact h1
  have hZ : ∀ i, ∃ c, c * (p : WittVector p S) = Wv i := fun i =>
    Ideal.mem_span_singleton'.mp ((WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr (hW0 i))
  choose Z₁ hZ₁ using hZ
  refine ⟨B, Z₁, Y₁, fun i => by linear_combination hY₁ i, fun i => ?_⟩
  have hp : (p : WittVector p K) ≠ 0 := WittVector.p_nonzero p K
  apply mul_left_cancel₀ hp
  have := hWimg i
  rw [← hZ₁ i, map_mul, map_natCast] at this
  linear_combination -this

end GlobalTheory.LemY
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

theorem digits (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p]
    [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ)
    (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Y : Fin d → WittVector p K)
    (hY : ∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i) (n : ℕ) :
    ∃ (B Z : Fin d → WittVector p S) (Yn : Fin d → WittVector p K),
      (∀ i, Y i = WittVector.map (algebraMap S K) (B i) + (p : WittVector p K) ^ n * Yn i) ∧
      ∀ i, WittVector.frobenius (Yn i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Yn) i
        + WittVector.map (algebraMap S K) (Z i) := by
  induction n with
  | zero =>
    exact ⟨0, 0, Y, fun i => by simp, fun i => by simpa using hY i⟩
  | succ n ih =>
    obtain ⟨B, Z, Yn, h1, h2⟩ := ih
    obtain ⟨B', Z', Y', h3, h4⟩ := GlobalTheory.LemY.step p S K d U Z Yn h2
    refine ⟨fun i => B i + (p : WittVector p S) ^ n * B' i, Z', Y', fun i => ?_, h4⟩
    rw [h1 i, h3 i, map_add, map_mul, map_pow, map_natCast]
    ring

theorem coeff_add_p_pow_mul_lt (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [CharP K p] (n k : ℕ)
    (hk : k < n) (a y : WittVector p K) : (a + (p : WittVector p K) ^ n * y).coeff k = a.coeff k := by
  have h := (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (x := a + (p : WittVector p K) ^ n * y)
    (y := a) (n := n)).2 (fun m hm => by
      rw [add_sub_cancel_left, mul_comm]
      exact WittVector.mul_pow_charP_coeff_zero _ hm)
  exact h k hk

theorem range_of_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Y : Fin d → WittVector p K), (∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i) → ∀ i, Y i ∈ (WittVector.map (p := p) (algebraMap S K)).range := by
  intro p _ S K _ _ _ _ _ _ _ _ _ _ d U Y hY i
  have hc : ∀ k, ∃ s : S, algebraMap S K s = (Y i).coeff k := by
    intro k
    obtain ⟨B, Z, Yn, h1, -⟩ := digits p S K d U Y hY (k + 1)
    refine ⟨(B i).coeff k, ?_⟩
    rw [h1 i, coeff_add_p_pow_mul_lt p (k + 1) k (Nat.lt_succ_self k), WittVector.map_coeff]
  choose c hc using hc
  refine ⟨WittVector.mk p c, ?_⟩
  ext k
  rw [WittVector.map_coeff]
  exact hc k

end GlobalTheory.LemY
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

theorem perfectRing_fractionRing (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S]
    [CharP S p] [PerfectRing S p] :
    haveI : CharP (FractionRing S) p :=
      charP_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S)) p
    PerfectRing (FractionRing S) p := by
  haveI : CharP (FractionRing S) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S)) p
  refine PerfectRing.ofSurjective _ p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨a', rfl⟩ := surjective_frobenius S p a
  obtain ⟨b', rfl⟩ := surjective_frobenius S p b
  refine ⟨algebraMap S (FractionRing S) a' / algebraMap S (FractionRing S) b', ?_⟩
  simp [frobenius_def, div_pow, map_pow]

theorem dvd_of_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] (d : ℕ) (m : WittVector p S) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Z : Fin d → WittVector p S), m.coeff 0 ≠ 0 → (∀ i, m * WittVector.frobenius (Z i) = WittVector.frobenius m * (U *ᵥ Z) i) → ∀ i, m ∣ Z i := by
  intro p _ S _ _ _ _ _ d m U Z hm hZ i
  let K := FractionRing S
  haveI : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective S K) p
  haveI : PerfectRing K p := perfectRing_fractionRing p S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  set j : WittVector p S →+* WittVector p K := WittVector.map (algebraMap S K) with hj
  have jinj : Function.Injective j := WittVector.map_injective _ hinj
  have hm' : (j m).coeff 0 ≠ 0 := by
    rw [hj, WittVector.map_coeff]
    exact fun h => hm (hinj (by simpa using h))
  obtain ⟨u, hu⟩ := WittVector.isUnit_of_coeff_zero_ne_zero (j m) hm'
  let Y : Fin d → WittVector p K := fun k => ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * j (Z k)
  have hfj : ∀ x, WittVector.frobenius (j x) = j (WittVector.frobenius x) := fun x =>
    (map_frobenius_charP p (algebraMap S K) x).symm

  have hφu : WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
      * WittVector.frobenius (u : WittVector p K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hY : ∀ k, WittVector.frobenius (Y k) = (U.map j *ᵥ Y) k := by
    intro k
    have e := congrArg j (hZ k)
    rw [map_mul, map_mul, ← hfj, ← hfj, map_mulVec_witt p (algebraMap S K) d U Z k, ← hu] at e

    have hmv : (U.map j *ᵥ Y) k = ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
        * (U.map j *ᵥ fun l => j (Z l)) k := by
      simp only [Y, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [hmv]
    simp only [Y, map_mul]
    calc WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * WittVector.frobenius (j (Z k))
        = WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
          * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * ((u : WittVector p K) * WittVector.frobenius (j (Z k)))) := by
          rw [← mul_assoc (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)), Units.inv_mul, one_mul]
      _ = WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
          * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (WittVector.frobenius (u : WittVector p K) * (U.map j *ᵥ fun l => j (Z l)) k)) := by
          rw [e]
      _ = (WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * WittVector.frobenius (u : WittVector p K))
          * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (U.map j *ᵥ fun l => j (Z l)) k) := by ring
      _ = _ := by rw [hφu, one_mul]
  obtain ⟨w, hw⟩ := range_of_frobenius_eq p S K d U Y hY i
  refine ⟨w, jinj ?_⟩
  rw [map_mul, ← hu]
  change j w = Y i at hw
  rw [hw]
  simp only [Y, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.LemY
end
