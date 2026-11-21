import Mathlib
import Formalism.DistinguishedUnitIdeals.PhiFreeOfBasis
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GoodOf
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEPrim

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace PolynomialValuationLemmas

theorem factV {O : Type} [CommRing O] [IsLocalRing O] {ℓ : ℕ} {u x : Oˣ} (hp : ℓ.Prime)
    (h3 : 3 ≤ ℓ) (hl : ¬ IsUnit (ℓ : O)) (hu : (u : O) = 1 + (ℓ : O) * (x : O)) :
    FactVval u ℓ := by
  have key : ∀ r : ℕ, 1 ≤ r →
      ∃ ε : Oˣ, (u : O) ^ r - 1 = (ε : O) * (ℓ : O) ^ (1 + padicValNat ℓ r) := by
    intro r hr
    rw [hu]
    exact GoodPlacesAlt.one_add_pow_sub_one_valuation hp h3 hl x.isUnit r hr
  intro m hm
  obtain ⟨r, rfl | rfl⟩ := m.eq_nat_or_neg
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd rfl hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨-ε, ?_⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val, padicValInt.of_nat, Units.val_neg]
    linear_combination -hε
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd (by simp) hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨(u ^ r)⁻¹ * ε, ?_⟩
    have hv : padicValInt ℓ (-(r : ℤ)) = padicValNat ℓ r := by simp [padicValInt]
    have hinv : (((u ^ r)⁻¹ : Oˣ) : O) * (u : O) ^ r = 1 := by
      rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
    rw [zpow_neg, zpow_natCast, hv, Units.val_mul]
    linear_combination (((u ^ r)⁻¹ : Oˣ) : O) * hε - hinv

theorem val_mul_pow (ℓ E : ℕ) [Fact ℓ.Prime] {i : ℤ} (hi : i ≠ 0) :
    padicValInt ℓ (i * ((ℓ ^ E : ℕ) : ℤ)) = E + padicValInt ℓ i := by
  have h2 : ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  rw [padicValInt.mul hi h2, padicValInt.of_nat, padicValNat.prime_pow, add_comm]

theorem ppevalVal {O : Type} [CommRing O] (u : Oˣ) (ℓ E : ℕ) (JS : Finset ℤ) (hp : ℓ.Prime)
    (hV : FactVval u ℓ) :
    ∃ ε : Oˣ, (G.PPoly u ℓ E JS).eval 1 = (ε : O) * (ℓ : O) ^ kapExp ℓ E JS := by
  haveI := Fact.mk hp
  have hf : ∀ i ∈ JS.erase 0, ∃ ε : Oˣ, (1 : O) - ((u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : Oˣ) : O) =
      (ε : O) * (ℓ : O) ^ (1 + E + padicValInt ℓ i) := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hm : i * ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := mul_ne_zero hi0 (by exact_mod_cast pow_ne_zero _ hp.ne_zero)
    obtain ⟨ε, hε⟩ := hV _ hm
    refine ⟨ε, ?_⟩
    rw [hε, val_mul_pow ℓ E hi0, add_assoc]
  choose! ε hε using hf
  refine ⟨∏ i ∈ JS.erase 0, ε i, ?_⟩
  unfold kapExp
  rw [G.PPoly, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Units.coe_prod]
  push_cast
  rw [pow_add]
  ring

theorem ppval_of_le {O : Type} [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ)
    (hp : ℓ.Prime) (hV : FactVval u ℓ) (hk : kapExp ℓ E JS + kapExp ℓ E JS' ≤ 2 * kap) :
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS') := by
  obtain ⟨ε, h1⟩ := ppevalVal u ℓ E JS hp hV
  obtain ⟨ε', h2⟩ := ppevalVal u ℓ E JS' hp hV
  exact ⟨kapExp ℓ E JS + kapExp ℓ E JS', ε * ε', hk, by rw [h1, h2, Units.val_mul, pow_add]; ring⟩

theorem sum_le_sum_cover {K : ℕ} (W : Fin K → Finset ℤ) (S : Finset ℤ)
    (hS : ∀ i ∈ S, ∃ k, i ∈ W k) (g : ℤ → ℕ) :
    ∑ i ∈ S, g i ≤ ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
  calc ∑ i ∈ S, g i ≤ ∑ i ∈ S, ∑ k, if i ∈ W k then g i else 0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨k, hk⟩ := hS i hi
        calc g i = (if i ∈ W k then g i else 0) := by rw [if_pos hk]
          _ ≤ ∑ k', if i ∈ W k' then g i else 0 :=
            Finset.single_le_sum (f := fun k' => if i ∈ W k' then g i else 0) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
    _ = ∑ k, ∑ i ∈ S, if i ∈ W k then g i else 0 := Finset.sum_comm
    _ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
        simp only [Finset.sum_filter]

theorem cover {JS : Finset ℤ} {K : ℕ} {a : Fin K → ℤ} {y : Fin K → ℕ} {R : ℕ}
    (h : InWindows JS K a y R) :
    ∀ i ∈ JS.erase 0, ∃ k, i ∈ Finset.Ico (a k) (a k + (y k : ℤ)) := by
  intro i hi
  have h1 := h.1 (Finset.mem_of_mem_erase hi)
  rw [Finset.mem_biUnion] at h1
  obtain ⟨k, -, hk⟩ := h1
  exact ⟨k, hk⟩


theorem card_le {JS : Finset ℤ} {K : ℕ} {a : Fin K → ℤ} {y : Fin K → ℕ} {R : ℕ}
    (h : InWindows JS K a y R) : (JS.erase 0).card ≤ ∑ k, y k := by
  calc (JS.erase 0).card = ∑ i ∈ JS.erase 0, 1 := by simp
    _ ≤ ∑ k, ∑ i ∈ (JS.erase 0).filter (fun i => i ∈ Finset.Ico (a k) (a k + (y k : ℤ))), 1 :=
        sum_le_sum_cover (fun k => Finset.Ico (a k) (a k + (y k : ℤ))) _ (cover h) (fun _ => 1)
    _ ≤ ∑ k, y k := Finset.sum_le_sum fun k _ => by
        rw [← Finset.card_eq_sum_ones]
        calc _ ≤ (Finset.Ico (a k) (a k + (y k : ℤ))).card :=
              Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
          _ = y k := by simp


section free
variable {O : Type} [CommRing O]




variable {B : Base O} {n : ℕ} {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀]

theorem phiIt_smul (L₀ : Lat B n V₀) (e₀ : V₀) (h : ∀ i, L₀.φ i e₀ = e₀) (i : ZMod n) (k : ℕ)
    (a : PowerSeries O) : L₀.phiIt i k (a • e₀) = (⇑B.φ)^[k] a • e₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Lat.phiIt]
    rw [ih, L₀.φ_semi, h, Function.iterate_succ_apply']



end free

end PolynomialValuationLemmas

open PolynomialValuationLemmas

theorem factorial_valuation_holds : FactVvalOf := by
  intro O _ _ ℓ u x hp h3 hl hu
  exact factV hp h3 hl hu

theorem factorial_bound_holds : FactVOf := by
  intro O LL Ks Δ _ _ _ _ _ Lev u ℓ hu hl hV m hm h1
  obtain ⟨ε, hε⟩ := hV m hm
  have hU : Lev.u = Units.map (algebraMap O LL : O →* LL) u := Units.ext hu
  have h2 : algebraMap O LL ((u ^ m : Oˣ) : O) = 1 := by
    have : ((Lev.u ^ m : LLˣ) : LL) = algebraMap O LL ((u ^ m : Oˣ) : O) := by
      rw [hU, ← map_zpow]
      rfl
    rw [← this, h1, Units.val_one]
  have h3 := congrArg (algebraMap O LL) hε
  rw [map_sub, map_one, h2, sub_self, map_mul, map_pow, map_natCast] at h3
  exact mul_ne_zero ((ε.isUnit.map (algebraMap O LL)).ne_zero) (pow_ne_zero _ hl) h3.symm


theorem polynomial_valuation_holds : PPvalOf := by
  intro O _ u ℓ E kap JS JS' hp hV h
  exact ppval_of_le u ℓ E kap JS JS' hp hV (by unfold kapExp; omega)












end Formalism.ExponentWindows.E
