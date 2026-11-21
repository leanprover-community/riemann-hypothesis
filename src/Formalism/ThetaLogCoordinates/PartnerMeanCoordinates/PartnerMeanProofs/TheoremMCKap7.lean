import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.Statement
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMCB
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictedSaturationHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjectionPos
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundPosOfProjSat
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.FinalLL

section
namespace Formalism.InvariantFactorPaths.MC.GI

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas

variable {p : ℕ} [hp : Fact p.Prime]

def kapE (N r B : ℕ) : ℕ := (N + 4) * (r * B) + 6 * B


section term2
variable {N r : ℕ}

theorem term_valE (LL : Letters (N + 1)) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hk : ∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k))
    (hW : δv δ (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) - j)
    (hY : δv δ (Fin.last (N + 1)) = LL.total - (j - a))
    (d1 d2 : ℕ) (hd1 : padicValNat p a.factorial ≤ padicValNat p d1) (hd1' : d1 ≠ 0)
    (hd2 : padicValNat p a'.factorial ≤ padicValNat p d2) (hd2' : d2 ≠ 0) :
    -(kapE N r B : ℤ) + ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))) +
      ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ))) -
      (padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) +
      (padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) : ℤ) ≤ 0 := by
  have hpp : p.Prime := hp.out
  have hF : ∀ n : ℕ, n.factorial ≠ 0 := fun n => Nat.factorial_ne_zero n
  have hmul : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → padicValNat p (x * y) = padicValNat p x + padicValNat p y :=
    fun x y hx hy => padicValNat.mul hx hy
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ), (∀ i, f i ≠ 0) →
      padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
    intro ι s f hf
    classical
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro x s hx ih
      rw [Finset.prod_insert hx, Finset.sum_insert hx,
        hmul _ _ (hf x) (Finset.prod_ne_zero_iff.2 (fun i _ => hf i)), ih]
  have hlog : ∀ m, m ≤ LL.total + LL.deg (Fin.last N) + r → Nat.log p m ≤ B :=
    fun m hm => (Nat.log_mono_right hm).trans hB
  have hch : ∀ n k : ℕ, n ≤ LL.total + LL.deg (Fin.last N) + r → padicValNat p (n.choose k) ≤ B := by
    intro n k hn
    rw [← Nat.factorization_def _ hpp]
    exact Nat.factorization_choose_le_log.trans (hlog n hn)
  have hsplit : ∀ n k : ℕ, k ≤ n → padicValNat p n.factorial =
      padicValNat p (n.choose k) + padicValNat p k.factorial + padicValNat p (n - k).factorial := by
    intro n k hk
    rw [← Nat.choose_mul_factorial_mul_factorial hk,
      hmul _ _ (mul_ne_zero (Nat.choose_pos hk).ne' (hF _)) (hF _),
      hmul _ _ (Nat.choose_pos hk).ne' (hF _)]
  have hgroup : ∀ (s : Finset (Fin r)) (x : Fin r → ℕ),
      ∑ i ∈ s, x i ≤ LL.total + LL.deg (Fin.last N) + r →
      padicValNat p (∑ i ∈ s, x i).factorial ≤ ∑ i ∈ s, padicValNat p (x i).factorial + s.card * B := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · intro _; simp
    · intro y s hy ih hle
      rw [Finset.sum_insert hy] at hle
      rw [Finset.sum_insert hy, Finset.sum_insert hy, Finset.card_insert_of_notMem hy]
      have h1 := hsplit (x y + ∑ i ∈ s, x i) (x y) (Nat.le_add_right _ _)
      rw [Nat.add_sub_cancel_left] at h1
      have h2 := hch (x y + ∑ i ∈ s, x i) (x y) hle
      have h3 := ih (le_trans (Nat.le_add_left _ _) hle)
      rw [h1]
      nlinarith
  have hT : ∀ i, LL.deg i ≤ LL.total := fun i => by
    unfold Letters.total
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hD : LL.deg (Fin.last N) ≤ LL.total := hT _
  have hδv : ∀ k, δv δ k = ∑ ρ, δ (k, ρ) := fun _ => rfl
  have hgδ : ∀ k, δv δ k ≤ LL.total + LL.deg (Fin.last N) + r →
      padicValNat p (δv δ k).factorial ≤ ∑ ρ, padicValNat p (δ (k, ρ)).factorial + r * B := by
    intro k hk
    rw [hδv] at hk ⊢
    have h := hgroup Finset.univ (fun ρ => δ (k, ρ)) hk
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hC1 : j.choose a ≠ 0 := (Nat.choose_pos ha).ne'
  have hC2 : j.choose a' ≠ 0 := (Nat.choose_pos ha').ne'
  have hCDj : (LL.deg (Fin.last N)).choose j ≠ 0 := (Nat.choose_pos hj).ne'
  have hPne : ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun v _ => hF _)
  have hP2 : ∏ i, (LL.deg i).factorial ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hF _)
  have P1 : padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) =
      padicValNat p (j.choose a) + padicValNat p (j.choose a') + padicValNat p d1 + padicValNat p d2 +
        padicValNat p a'.factorial +
        ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin r, padicValNat p (δ (k, ρ)).factorial := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _)) hPne,
      hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _),
      hmul _ _ (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2',
      hmul _ _ (mul_ne_zero hC1 hC2) hd1', hmul _ _ hC1 hC2, hprod _ _ (fun v => hF _),
      Fintype.sum_prod_type]
  have P2 : padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) =
      padicValNat p ((LL.deg (Fin.last N)).choose j) +
        (padicValNat p j.factorial + padicValNat p j.factorial) +
        padicValNat p LL.total.factorial + ∑ i, padicValNat p (LL.deg i).factorial := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _)) hP2,
      hmul _ _ (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _),
      hmul _ _ hCDj (pow_ne_zero _ (hF _)), sq, hmul _ _ (hF _) (hF _), hprod _ _ (fun i => hF _)]
  have S1 : ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin r, padicValNat p (δ (k, ρ)).factorial =
      ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial +
        ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.last N), ρ)).factorial +
        ∑ ρ : Fin r, padicValNat p (δ (Fin.last (N + 1), ρ)).factorial := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have S2 : ∑ i, padicValNat p (LL.deg i).factorial =
      ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial +
        padicValNat p (LL.deg (Fin.last N)).factorial := by
    rw [Fin.sum_univ_castSucc]
  have G1 : ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial ≤
      ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial +
        N * (r * B) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun k _ => by
      have hk' := hgδ (Fin.castSucc (Fin.castSucc k)) (by rw [hk k]; have := hT (Fin.castSucc k); omega)
      rw [hk k] at hk'
      exact hk')
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    exact h
  have GW := hgδ (Fin.castSucc (Fin.last N)) (by rw [hW]; omega)
  rw [hW] at GW
  have GY := hgδ (Fin.last (N + 1)) (by rw [hY]; omega)
  rw [hY] at GY
  have hja : j - a ≤ LL.total := by omega
  have E1 := hsplit j a ha
  have E2 := hsplit j a' ha'
  have E3 := hsplit (LL.deg (Fin.last N)) j hj
  have E4 := hsplit LL.total (j - a) hja
  have B1 := hch (LL.deg (Fin.last N)) j (by omega)
  have B2 := hch LL.total (j - a) (by omega)
  have B3 := hch j a' (by omega)
  rw [P1, P2, S1, S2]
  unfold kapE
  push_cast
  nlinarith

end term2

section term3
variable {N r : ℕ}

theorem termF_IVPE (LL : Letters (N + 1)) (ρ : Fin r) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (z j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hβd : δv β + (j - a) • eWY = (LL.snoc LL.total).deg) (hβp : β (xW ρ) ≤ β (yE ρ))
    (hγd : δv γ + (j - a') • eWY = (LL.snoc LL.total).deg) (hγp : γ (xW ρ) ≤ γ (yE ρ))
    (h h' : ℚ_[p])
    (hh : ‖h‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))))
    (hh' : ‖h'‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ)))) :
    IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kapE N r B) * termF LL ρ z j a a' β γ h h' m) := by
  have hxy := xW_ne_yE (N := N) ρ
  set s : Fin (N + 1 + 1) × Fin r →₀ ℕ := Finsupp.single (xW ρ) 1 + Finsupp.single (yE ρ) 1 with hs
  by_cases h1 : β (xW ρ) < a
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial, Dop_pow_monomial_lt _ _ hxy a _ h
      (by simp [Finsupp.single_apply, hxy]; exact h1), fock_zero_left]
    simp
  by_cases h2 : γ (xW ρ) < a'
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial (yE ρ) m γ, Dop_pow_monomial_lt _ _ hxy a' _ h'
      (by simp [Finsupp.single_apply, hxy]; exact h2), fock_zero_right']
    simp
  push_neg at h1 h2
  have hle : ∀ (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (t : ℕ), t ≤ δ (xW ρ) → δ (xW ρ) ≤ δ (yE ρ) → t • s ≤ δ := by
    intro δ t ht1 ht2 v
    simp only [hs, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hv1 : xW ρ = v
    · subst hv1; simp [Ne.symm hxy]; exact ht1
    · by_cases hv2 : yE ρ = v
      · subst hv2; simp [hv1]; omega
      · simp [hv1, hv2]
  obtain ⟨β₀, rfl⟩ : ∃ β₀, β = β₀ + a • s := ⟨β - a • s, (tsub_add_cancel_of_le (hle β a h1 hβp)).symm⟩
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀, γ = γ₀ + a' • s := ⟨γ - a' • s, (tsub_add_cancel_of_le (hle γ a' h2 hγp)).symm⟩
  by_cases hb : β₀ = γ₀
  swap
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [fock_Dop_term _ _ hxy, if_neg hb]
    simp
  subst hb
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  have hoS : o ≤ S := deg_le_total LL (Fin.last N)

  have hsδ : ∀ t : ℕ, δv (t • s) = Pi.single (Fin.castSucc (Fin.last N)) t + Pi.single (Fin.last (N + 1)) t := by
    intro t
    rw [hs, smul_add, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one, δv_add,
      δv_single', δv_single']
  have hβd' : δv β₀ + Pi.single (Fin.castSucc (Fin.last N)) a + Pi.single (Fin.last (N + 1)) a + (j - a) • eWY =
      (LL.snoc LL.total).deg := by
    rw [← hβd, δv_add, hsδ, add_assoc (δv β₀)]
  obtain ⟨hk, hW, hY⟩ := comp_facts LL (j - a) β₀ a a hβd'
  set e := β₀ (yE ρ) + a with he
  set e' := β₀ (yE ρ) + a' with he'
  have heS : e ≤ S - (j - a) := by
    have := le_δv β₀ (Fin.last (N + 1)) ρ
    simp only [yE] at he
    omega
  set c1 := o + S + r + z - 1 - j with hc1
  set d1 := (β₀ (xW ρ) + a).descFactorial a with hd1
  set d2 := (β₀ (xW ρ) + a').descFactorial a' with hd2
  set δh := β₀ + Finsupp.single (yE ρ) a with hδh
  set Num := j.choose a * j.choose a' * d1 * d2 * a'.factorial * ∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial
    with hNum
  set Den := o.choose j * j.factorial ^ 2 * S.factorial * ∏ i, (LL.deg i).factorial with hDen
  set K : ℚ_[p] := (p : ℚ_[p]) ^ (kapE N r B) * ((-1 : ℚ_[p]) ^ j * h * h' * (Num : ℚ_[p]) / (Den : ℚ_[p]))
    with hK
  have nd1 : d1 ≠ 0 := by
    rw [hd1]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have nd2 : d2 ≠ 0 := by
    rw [hd2]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have hNum0 : Num ≠ 0 := by
    rw [hNum]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero
      (Nat.choose_pos ha).ne' (Nat.choose_pos ha').ne') nd1) nd2) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos hj).ne'
      (pow_ne_zero _ (Nat.factorial_pos _).ne')) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')

  have hδv : δv δh = δv β₀ + Pi.single (Fin.last (N + 1)) a := by rw [hδh, δv_add, δv_single']
  have hne : ∀ k : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc k :=
    fun k h => Fin.castSucc_ne_last k h.symm
  have hKn : ‖K‖ ≤ 1 := by
    rw [hK]
    refine norm_K _ h h' _ _ hh hh' Num Den hNum0 hDen0 _ (by simp) ?_
    rw [hNum, hDen]
    refine term_valE LL hr B hB j a a' hj ha ha' δh ?_ ?_ ?_ d1 d2 ?_ nd1 ?_ nd2
    · intro k
      rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (hne _).symm, add_zero, hk k]
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (Fin.castSucc_ne_last _), add_zero]; omega
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_pos rfl]; omega
    · rw [hd1]; exact vdesc_ge _ _ (by omega)
    · rw [hd2]; exact vdesc_ge _ _ (by omega)
  have I1 := ((IVP.choose_add (p := p) c1 (o - j)).mul (IVP.choose_add e e)).mul (IVP.choose_add e' a')
  refine ((I1.smul K hKn).mono (by omega)).congr ?_
  intro m
  unfold termF
  rw [fock_Dop_term _ _ hxy, if_pos rfl, Nat.add_sub_cancel]
  have hjM : j ≤ o + (m + S) + r + z - 1 := by omega
  have hMj : o + (m + S) + r + z - 1 - j = m + c1 := by omega
  have hMo : (((o + (m + S) + r + z - 1).choose o : ℕ) : ℚ_[p]) =
      (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) *
        (((o + (m + S) + r + z - 1 - j).choose (o - j) : ℕ) : ℚ_[p]) / ((o.choose j : ℕ) : ℚ_[p]) := by
    have := Nat.choose_mul (n := o + (m + S) + r + z - 1) (k := o) (s := j) hj
    rw [eq_div_iff (by exact_mod_cast (Nat.choose_pos hj).ne')]
    exact_mod_cast this
  rw [hMo, hMj, Nat.descFactorial_eq_factorial_mul_choose (m + e') a']
  have hwf : wf (p := p) δh = ((∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial : ℕ) : ℚ_[p]) := by
    unfold wf; push_cast; rfl
  rw [hwf, hK, hNum, hDen]
  have n1 : (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjM).ne'
  have n2 : ((o.choose j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have n3 : ((j.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n4 : ((S.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n5 : ((m.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n6 : ((∏ i, (LL.deg i).factorial : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  push_cast at n6 ⊢
  rw [← hd1, ← hd2, ← he, ← ho, ← hS]
  have hc := mul_inv_cancel₀ n1
  have hm := mul_inv_cancel₀ n5
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-((p : ℚ_[p]) ^ kapE N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹)) * hc +
    (-((p : ℚ_[p]) ^ kapE N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹) *
      ((((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) * (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹)) * hm

end term3

end Formalism.InvariantFactorPaths.MC.GI

namespace Formalism.InvariantFactorPaths.MC

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas Formalism.InvariantFactorPaths.MC.GI

theorem gamma_integral_holds : GamIntC := by
  intro p _ N r LL ρ z f f' hr hW hf hf'
  set B := Nat.log p (LL.total + LL.deg (Fin.last N) + r) with hB
  have hκ : (N + 4) * (r * B) + 6 * B = kapE N r B := rfl
  have hwe : ∀ c : Fin r, wv (N := N) c ≠ ev c := by
    intro c; simp [wv, ev, Fin.castSucc_ne_last]

  have facts : ∀ g : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p], g ∈ PolZ p r LL →
      (∀ b ≤ LL.total + LL.deg (Fin.last N) + r, ∀ β,
        ‖coeff β ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g))‖ ≤
          (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)))) ∧
      (∀ b, ∀ β ∈ ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g)).support,
        δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) := by
    intro g hg
    have hgP : g ∈ Pol p r LL := (Submodule.mem_inf.mp hg).1
    have hgI : g ∈ IntPol p (Fin (N + 1) × Fin r) := (Submodule.mem_inf.mp hg).2
    have hG := aeval_int LL ρ g (intPol_coeff g hgI)
    have hGg := aeval_good LL ρ hW g hgP
    refine ⟨fun b hb β => ?_, ?_⟩
    · have h1 := FT_pow_coeff_norm (p := p) wv ev hwe (LL.total + LL.deg (Fin.last N) + r) B le_rfl 1
        (aeval (freezeSub p LL ρ) g) hG (univ.erase ρ) b hb β
      refine h1.trans ?_
      rw [one_mul]
      apply zpow_mono'
      have : (univ.erase ρ).card * B ≤ r * B := by
        apply Nat.mul_le_mul_right
        rw [card_erase_of_mem (mem_univ ρ), card_univ, Fintype.card_fin]; omega
      have : (((univ.erase ρ).card * B : ℕ) : ℤ) ≤ ((r * B : ℕ) : ℤ) := by exact_mod_cast this
      linarith
    · refine supp_FT_pow wv ev (univ.erase ρ)
        (fun b β => δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) ?_ hwe _ ?_
      · intro b β c hc ⟨h1, h2⟩
        have hcρ : c ≠ ρ := ne_of_mem_erase hc
        refine ⟨?_, ?_⟩
        · rw [← h1, δv_add, δv_add, δv_single, δv_single, succ_nsmul, eWY]
          abel
        · simpa [Finsupp.single_apply, xW, yE, wv, ev, hcρ, Ne.symm hcρ, Fin.castSucc_ne_last] using h2
      · intro β hβ
        obtain ⟨h1, h2⟩ := hGg β hβ
        exact ⟨by rw [zero_smul, add_zero]; exact h1, h2⟩
  obtain ⟨hc1, hs1⟩ := facts f hf
  obtain ⟨hc2, hs2⟩ := facts f' hf'
  have hIVP : IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kapE N r B) * tieGam p LL ρ z (m + LL.total) f f') := by
    simp only [tieGam_expand, Finset.mul_sum]
    apply IVP.sum; intro j hj
    apply IVP.sum; intro a ha
    apply IVP.sum; intro a' ha'
    apply IVP.sum; intro β hβ
    apply IVP.sum; intro γ hγ
    rw [mem_range] at hj ha ha'
    have hjo : j ≤ LL.deg (Fin.last N) := by omega
    have hoS := deg_le_total LL (Fin.last N)
    obtain ⟨hβd, hβp⟩ := hs1 (j - a) β hβ
    obtain ⟨hγd, hγp⟩ := hs2 (j - a') γ hγ
    exact termF_IVPE LL ρ hr B le_rfl z j a a' hjo (by omega) (by omega) β γ hβd hβp hγd hγp _ _
      (hc1 (j - a) (by omega) β) (hc2 (j - a') (by omega) γ)
  obtain ⟨c, hc⟩ := hIVP.toChoose (S := LL.total)
  refine ⟨c, fun n hn => ?_⟩
  have := hc n hn
  simp only [Nat.sub_add_cancel hn] at this
  rw [hκ]
  exact this

end Formalism.InvariantFactorPaths.MC
end

section
namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset

theorem partner_condition_holds : YPartnerC := by
  intro p _ N r _ _ LL q J M ρ e1 hr hHP z hz hprim
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin (N + 1) → Set (Fin r → ℤ) := fun j =>
    {la | ∀ k, min (J k) N = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin (N + 1), ∃ P, IsTypeProj p LL j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (Nat.lt_succ_iff.mp j.isLt) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL := fun j => typeProj_pol LL j (Tj j) (P j) (hPt j)

  have hfixY : ∀ j : Fin (N + 1), ∀ x ∈ Y p (r := r) LL J M, P j x = x := by
    intro j
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r LL ⊓ ⨅ (k : Fin q) (_ : min (J k) N = (j : ℕ)), YCond p (r := r) LL j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r LL ∧ ∀ k, min (J k) N = (j : ℕ) → x ∈ YCond p (r := r) LL j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix LL j (Tj j) (P j) (hPt j) S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨glAct_pol LL j c d x hx.1, fun k hk => ycond_glStable LL j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol j x hx.1, fun k hk => typeProj_ycond LL j (Tj j) (P j) (hPt j) (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp LL j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    intro x hx
    apply hfix
    rw [hmemS]
    refine ⟨(Submodule.mem_inf.mp hx).1, fun k hk => ?_⟩
    have := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 k
    rw [ycond_min, hk] at this
    exact this

  have hranY : ∀ j : Fin (N + 1), ∀ u, P j u = u → ∀ k, min (J k) N = (j : ℕ) →
      u ∈ YCond p (r := r) LL (J k) (M k) := by
    intro j u hu k hk
    rw [ycond_min, hk]
    have h1 : u ∈ LinearMap.range (P j) := ⟨u, hu⟩
    rw [(hPt j).2.1] at h1
    exact (iSup₂_le fun la hla => isoC_le_ycond LL j la (M k) (hla k hk)) h1

  obtain ⟨m0, hm0⟩ := prim_unit_coeff LL J M z hz hprim
  have hzY : z ∈ Y p (r := r) LL J M := (Submodule.mem_inf.mp hz).1
  have hzP : z ∈ Pol p r LL := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1
  have hm0mem : m0 ∈ z.support := by
    rw [mem_support_iff]; intro h; rw [h, norm_zero] at hm0; exact zero_ne_one hm0
  have hmd : MultiDeg LL m0 := by
    rw [Pol, mem_restrictSupport_iff] at hzP; exact hzP (Finset.mem_coe.mpr hm0mem)
  have hmonZ : (monomial m0 (1 : ℚ_[p])) ∈ PolZ p r LL := by
    classical
    refine Submodule.mem_inf.mpr ⟨?_, mem_intPol_of_norm _ fun m => ?_⟩
    · show monomial m0 (1 : ℚ_[p]) ∈ Pol p r LL
      rw [Pol, mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_coe] at hm
      rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
      exact hmd
    · rw [coeff_monomial]; split_ifs <;> simp
  set u := lcomp P (List.finRange (N + 1)) (monomial m0 (1 : ℚ_[p])) with hu
  have hufix : ∀ j, P j u = u := fun j => lcomp_fix P hPP hcomm _ j (List.mem_finRange j) _
  have hint := lcomp_int LL e1 P hPpol hPint (List.finRange (N + 1)) _ hmonZ
  rw [List.length_finRange] at hint
  refine ⟨((p : ℚ_[p]) ^ (e1 * (N + 1))) • u, ?_, ?_⟩
  · refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hint).1, ?_⟩, hint⟩
    rw [Submodule.mem_iInf]
    intro k
    refine Submodule.smul_mem _ _ ?_
    exact hranY ⟨min (J k) N, by omega⟩ u (hufix _) k rfl
  ·
    rw [fockN_smul_right', norm_mul, norm_pow, Padic.norm_p]
    have hf : fockN p LL z u = fockN p LL z (monomial m0 1) := by
      unfold fockN
      rw [hu, lcomp_fock P hPsa z (fun j => hfixY j z hzY)]
    rw [hf]
    have hge := fockN_monomial_ge LL z m0 hmd hm0
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) = (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * 1 := by
          rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
      _ ≤ (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * ‖fockN p LL z (monomial m0 1)‖ :=
          mul_le_mul_of_nonneg_left hge (by positivity)

end Formalism.InvariantFactorPaths.MC
end

section
namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.InvariantFactorPaths.OddLevelGainBounds Formalism.InvariantFactorPaths.OddLevelGainBounds.TB Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset

theorem kap_num (N s : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (hN : N ≤ 2 * s + 2) :
    (3 / 2 : ℝ) * (((N : ℝ) + 2) * Q) ≤ 3 * ((s : ℝ) + 2) * Q := by
  have h : (N : ℝ) ≤ 2 * (s : ℝ) + 2 := by exact_mod_cast hN
  nlinarith

end Formalism.InvariantFactorPaths.MC
end
