import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.InhabCAR
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem csq_sum_univ_pm {R : Type*} [AddCommMonoid R] (ε : Fin n → Bool) (f : Fin n → R) :
    ∑ a, f a = ∑ a ∈ plusIdx ε, f a + ∑ a ∈ minusIdx ε, f a := by
  unfold plusIdx minusIdx
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true) f]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp

theorem sum_comm_pair_pair {R : Type*} [AddCommMonoid R] {ι κ ι' κ' : Type*} (s : Finset ι) (s' : Finset ι')
    (t : Finset κ) (t' : Finset κ') (f : ι → ι' → κ → κ' → R) :
    ∑ a ∈ s, ∑ b ∈ s', ∑ i ∈ t, ∑ j ∈ t', f a b i j = ∑ i ∈ t, ∑ j ∈ t', ∑ a ∈ s, ∑ b ∈ s', f a b i j := by
  calc _ = ∑ a ∈ s, ∑ i ∈ t, ∑ b ∈ s', ∑ j ∈ t', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ s, ∑ i ∈ t, ∑ j ∈ t', ∑ b ∈ s', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ t, ∑ a ∈ s, ∑ j ∈ t', ∑ b ∈ s', f a b i j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem csq_filter_eq_plus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ plusIdx ε) :
    univ.filter (fun b => ε b = ε a) = plusIdx ε := by
  have h : ε a = true := by simpa [plusIdx] using ha
  ext b
  simp [plusIdx, h]

theorem csq_filter_eq_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    univ.filter (fun b => ε b = ε a) = minusIdx ε := by
  have h : ε a = false := by simpa [minusIdx] using ha
  ext b
  simp [minusIdx, h]

theorem casimirK_pm {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ M) :
    casimirK ε F = ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, F a b * F b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, F a b * F b a := by
  unfold casimirK
  rw [csq_sum_univ_pm ε]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_minus ε ha]

theorem csq_sgE_pp (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ plusIdx ε) (hb : b ∈ plusIdx ε) :
    sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by
  have ha' : ε a = true := by simpa [plusIdx] using ha
  have hb' : ε b = true := by simpa [plusIdx] using hb
  simp [sgE, ha', hb']

theorem csq_sgE_mm (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ minusIdx ε) (hb : b ∈ minusIdx ε) :
    sgE ε cp cm a b = -∑ i ∈ plusIdx ε, cp i b * cm i a := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  have hb' : ε b = false := by simpa [minusIdx] using hb
  simp [sgE, ha', hb']

theorem csq_two_rhoHol_plus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ plusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = (qOf ε : ℂ) := by
  have ha' : ε a = true := by simpa [plusIdx] using ha
  rw [show rhoHol ε a = (qOf ε : ℝ) / 2 by simp [rhoHol, ha']]
  push_cast
  ring

theorem csq_two_rhoHol_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = -(pOf ε : ℂ) := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  rw [show rhoHol ε a = -(pOf ε : ℝ) / 2 by simp [rhoHol, ha']]
  push_cast
  ring

theorem two_rho_sum {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Module.End ℂ M) :
    (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • F a =
      ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • F a - ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • F a := by
  rw [Finset.smul_sum, csq_sum_univ_pm ε, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_minus ε ha, neg_smul]


end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (i a j b : Fin n) :
    cm i a * cp j b = (if i = j ∧ a = b then 1 else 0) - cp j b * cm i a :=
  eq_sub_of_add_eq (hC i a j b).2.2

private theorem isCAR_cm_mul_cm_eq_neg_swap {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (i a j b : Fin n) :
    cm i a * cm j b = -(cm j b * cm i a) :=
  eq_neg_of_add_eq_zero_left (hC i a j b).2.1

private theorem sum_sum_ite_eq_eq_sum {R ι : Type*} [AddCommMonoid R] [DecidableEq ι] (s : Finset ι)
    (f : ι → R) : ∑ x ∈ s, ∑ y ∈ s, (if x = y then f x else 0) = ∑ x ∈ s, f x :=
  Finset.sum_congr rfl fun x hx => by simp [hx]

private theorem isCAR_cp_cm_cp_cm_reorder_shared_snd {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b x y : Fin n) :
    cp a x * cm b x * (cp b y * cm a y) =
      (if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y) := by
  rw [show cp a x * cm b x * (cp b y * cm a y) = cp a x * (cm b x * cp b y) * cm a y by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC b x b y]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hxy h.2), if_neg hxy]
    noncomm_ring

private theorem isCAR_cp_cm_cp_cm_reorder_shared_fst {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b i j : Fin n) :
    cp i b * cm i a * (cp j a * cm j b) =
      (if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b) := by
  rw [show cp i b * cm i a * (cp j a * cm j b) = cp i b * (cm i a * cp j a) * cm j b by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC i a j a]
  by_cases hij : i = j
  · subst hij
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hij h.1), if_neg hij]
    noncomm_ring

theorem casimirK_sgE {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool) :
    casimirK ε (sgE ε cp cm) = (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • sgE ε cp cm a a := by
  have hpos : ∀ a ∈ plusIdx ε, ∀ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ x ∈ minusIdx ε, ∑ y ∈ minusIdx ε,
          ((if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y)) := by
    intro a ha b hb
    rw [csq_sgE_pp ε cp cm ha hb, csq_sgE_pp ε cp cm hb ha, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => isCAR_cp_cm_cp_cm_reorder_shared_snd hC a b x y
  have hneg : ∀ a ∈ minusIdx ε, ∀ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε,
          ((if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b)) := by
    intro a ha b hb
    rw [csq_sgE_mm ε cp cm ha hb, csq_sgE_mm ε cp cm hb ha, neg_mul_neg,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => isCAR_cp_cm_cp_cm_reorder_shared_fst hC a b i j
  have hposBlock : ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (pOf ε : ℂ) •
            ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x -
          ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
            ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hpos a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const, ← Finset.smul_sum]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hnegBlock : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (qOf ε : ℂ) •
            ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b -
          ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
            ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hneg a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hT : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) =
      -∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
        ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [sum_comm_pair_pair, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [isCAR_cm_mul_cm_eq_neg_swap hC i a j b, mul_neg]
  have hN : ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b =
      ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.sum_comm]
  have hR1 : ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • sgE ε cp cm a a =
      (qOf ε : ℂ) •
        ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_pp ε cp cm ha ha]
  have hR2 : ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • sgE ε cp cm a a =
      -((pOf ε : ℂ) •
        ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b) := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_mm ε cp cm ha ha, smul_neg]
  rw [casimirK_pm, two_rho_sum, hposBlock,
    hnegBlock, hR1, hR2, hT, hN]
  abel

theorem csq_E_comm_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (x y a b : Fin n) :
    E x y * sgE ε cp cm a b = sgE ε cp cm a b * E x y := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← mul_assoc, (hEC x y a z).1, mul_assoc, (hEC x y b z).2, ← mul_assoc]
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, (hEC x y i b).1, mul_assoc, (hEC x y i a).2, ← mul_assoc]
  · rw [mul_zero, zero_mul]

def crossT (ε : Fin n → Bool) (E cp cm : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, E x y * sgE ε cp cm y x +
    ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, E a b * sgE ε cp cm b a

private theorem sum_sum_add_mul_add_of_commute (s : Finset (Fin n)) (E S : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b c d, S a b * E c d = E c d * S a b) :
    ∑ a ∈ s, ∑ b ∈ s, (E a b + S a b) * (E b a + S b a) =
      ∑ a ∈ s, ∑ b ∈ s, E a b * E b a + (2 : ℂ) • ∑ a ∈ s, ∑ b ∈ s, E a b * S b a +
        ∑ a ∈ s, ∑ b ∈ s, S a b * S b a := by
  have hsw : ∑ a ∈ s, ∑ b ∈ s, S a b * E b a = ∑ a ∈ s, ∑ b ∈ s, E a b * S b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h b a a b
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [hsw, two_smul]
  abel

theorem casimirK_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) :
    casimirK ε (diagE ε E cp cm) =
      casimirK ε E + (2 : ℂ) • crossT ε E cp cm + casimirK ε (sgE ε cp cm) := by
  have hc : ∀ a b c d, sgE ε cp cm a b * E c d = E c d * sgE ε cp cm a b :=
    fun a b c d => (csq_E_comm_sgE hEC ε c d a b).symm
  simp only [casimirK_pm, diagE, crossT]
  rw [sum_sum_add_mul_add_of_commute (plusIdx ε) E (sgE ε cp cm) hc,
    sum_sum_add_mul_add_of_commute (minusIdx ε) E (sgE ε cp cm) hc, smul_add]
  abel

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem csq_dd_pt {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (i a j b : Fin n) :
    E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a) =
      (if i = j then E a b * (cp i a * cm j b) else 0) - (if b = a then E j i * (cp i a * cm j b) else 0) +
        (if b = a then (if j = i then E i a * E a i else 0) else 0) := by
  have c1 : E j b * cp i a = cp i a * E j b := (hEC j b i a).1
  have c2 : E a i * cm j b = cm j b * E a i := (hEC a i j b).2
  have hcar : cm j b * cp i a = (if j = i ∧ b = a then 1 else 0) - cp i a * cm j b :=
    eq_sub_of_add_eq (hC j b i a).2.2
  have hgl : E a i * E j b =
      E j b * E a i + ((if i = j then E a b else 0) - (if b = a then E j i else 0)) := by
    rw [← hE a i j b]; abel
  have step : E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a) =
      E a i * E j b * (cp i a * cm j b) + E j b * E a i * (cm j b * cp i a) := by
    calc _ = E a i * (E j b * cp i a) * cm j b + E j b * (E a i * cm j b) * cp i a := by
            rw [c1, c2]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [step, hgl, hcar]
  rcases eq_or_ne i j with h1 | h1 <;> rcases eq_or_ne b a with h2 | h2
  · subst h1; subst h2
    simp only [eq_self_iff_true, and_self, if_true]
    noncomm_ring
  · subst h1
    simp only [eq_self_iff_true, if_true, h2, if_false, and_false]
    noncomm_ring
  · subst h2
    simp only [eq_self_iff_true, if_true, h1, Ne.symm h1, if_false, false_and]
    noncomm_ring
  · simp only [h1, h2, Ne.symm h1, if_false, and_false, false_and]
    noncomm_ring

theorem dd_add {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) :
    dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp =
      -(∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i) + crossT ε E cp cm := by
  have e1 : dOp ε E cp * dOp' ε E cm =
      -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        E a i * cp i a * (E j b * cm j b) := by
    unfold dOp dOp'
    rw [mul_neg, Finset.sum_mul_sum, neg_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_mul_sum]
    exact Finset.sum_comm
  have e2 : dOp' ε E cm * dOp ε E cp =
      -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        E j b * cm j b * (E a i * cp i a) := by
    unfold dOp dOp'
    rw [neg_mul, Finset.sum_mul_sum, neg_inj]
    simp only [Finset.sum_mul_sum]
    calc ∑ j ∈ plusIdx ε, ∑ i ∈ plusIdx ε, ∑ b ∈ minusIdx ε, ∑ a ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a)
        = ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε, ∑ a ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a) := Finset.sum_comm
      _ = ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hX : dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp =
      -(∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a))) := by
    rw [e1, e2]
    simp only [Finset.sum_add_distrib]
    abel
  have hA : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if i = j then E a b * (cp i a * cm j b) else 0) =
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a b * (cp i a * cm i b) := by
    have h1 : ∀ i ∈ plusIdx ε, ∀ a, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (if i = j then E a b * (cp i a * cm j b) else 0) =
        ∑ b ∈ minusIdx ε, E a b * (cp i a * cm i b) := by
      intro i hi a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_ite_eq, if_pos hi]
    refine (Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a _ => h1 i hi a).trans ?_
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm)
  have hB : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if b = a then E j i * (cp i a * cm j b) else 0) =
      ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, ∑ c ∈ minusIdx ε, E x y * (cp y c * cm x c) := by
    have h1 : ∀ i, ∀ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (if b = a then E j i * (cp i a * cm j b) else 0) =
        ∑ j ∈ plusIdx ε, E j i * (cp i a * cm j a) := by
      intro i a ha
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq', if_pos ha]
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a ha => h1 i a ha).trans ?_
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  have hC' : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if b = a then (if j = i then E i a * E a i else 0) else 0) =
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_congr rfl fun j _ => (by rw [Finset.sum_ite_eq', if_pos ha] :
      ∑ b ∈ minusIdx ε, (if b = a then (if j = i then E i a * E a i else 0) else 0) =
        (if j = i then E i a * E a i else 0))]
    rw [Finset.sum_ite_eq', if_pos hi]
  have hcross : crossT ε E cp cm =
      ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, ∑ c ∈ minusIdx ε, E x y * (cp y c * cm x c) -
        ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a b * (cp i a * cm i b) := by
    unfold crossT
    rw [sub_eq_add_neg]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      rw [csq_sgE_pp ε cp cm hy hx, Finset.mul_sum]
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [csq_sgE_mm ε cp cm hb ha, mul_neg, Finset.mul_sum]
  rw [hX]
  simp only [csq_dd_pt hE hC hEC, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB, hC', hcross]
  abel

private theorem sum_sum_ne_eps_eq_plusIdx_minusIdx_add (ε : Fin n → Bool) {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ¬ ε b = ε a), f a b =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, f x y + ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, f a b := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true)]
  have hm : univ.filter (fun a => ¬ ε a = true) = minusIdx ε := by
    ext a; simp [minusIdx]
  rw [hm]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [minusIdx, ha']
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [plusIdx, ha']

theorem two_D_sq {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) =
      -casimir E + casimirK ε (diagE ε E cp cm) -
        (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε E cp cm a a := by
  have hsq : (dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm) =
      dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp := by
    rw [add_mul, mul_add, mul_add, dOp_sq hE hC hEC, dOp'_sq hE hC hEC]
    abel
  have hs : ∑ a, ∑ b ∈ univ.filter (fun b => ¬ ε b = ε a), E a b * E b a =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a :=
    sum_sum_ne_eps_eq_plusIdx_minusIdx_add ε (fun a b => E a b * E b a)
  have hoff : casimir E = casimirK ε E +
      (∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a) := by
    rw [← hs]
    unfold casimir casimirK
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : ∀ a i : Fin n, E a i * E i a = E i a * E a i + (E a a - E i i) := by
    intro a i
    have h := hE a i i a
    rw [if_pos rfl, if_pos rfl] at h
    rw [← h]
    abel
  have hcomm2 : ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a i * E i a =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        (((plusIdx ε).card : ℂ) • ∑ a ∈ minusIdx ε, E a a -
          ((minusIdx ε).card : ℂ) • ∑ i ∈ plusIdx ε, E i i) := by
    rw [show ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a i * E i a =
        ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, (E i a * E a i + (E a a - E i i)) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => h1 a i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    refine congrArg₂ (· + ·) Finset.sum_comm (congrArg₂ (· - ·) ?_ ?_)
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
    · rw [Finset.sum_comm, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hrho : (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • E a a =
      ((minusIdx ε).card : ℂ) • ∑ i ∈ plusIdx ε, E i i -
        ((plusIdx ε).card : ℂ) • ∑ a ∈ minusIdx ε, E a a := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true)]
    have hm : univ.filter (fun a => ¬ ε a = true) = minusIdx ε := by
      ext a; simp [minusIdx]
    rw [hm]
    have e1 : ∑ a ∈ univ.filter (fun a => ε a = true), ((rhoHol ε a : ℝ) : ℂ) • E a a =
        (((minusIdx ε).card : ℂ) / 2) • ∑ i ∈ plusIdx ε, E i i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : ε a = true := (Finset.mem_filter.mp ha).2
      rw [show rhoHol ε a = ((minusIdx ε).card : ℝ) / 2 by simp [rhoHol, ha', qOf, minusIdx]]
      push_cast
      rfl
    have e2 : ∑ a ∈ minusIdx ε, ((rhoHol ε a : ℝ) : ℂ) • E a a =
        (-((plusIdx ε).card : ℂ) / 2) • ∑ a ∈ minusIdx ε, E a a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : ε a = false := (Finset.mem_filter.mp ha).2
      rw [show rhoHol ε a = -((plusIdx ε).card : ℝ) / 2 by simp [rhoHol, ha', pOf, plusIdx]]
      push_cast
      rfl
    rw [e1, e2, smul_add, smul_smul, smul_smul, sub_eq_add_neg, ← neg_smul]
    exact congrArg₂ (· + ·) (congrArg (· • _) (by ring)) (congrArg (· • _) (by ring))
  rw [hsq, dd_add hE hC hEC, casimirK_diagE hEC, casimirK_sgE hC, hoff, hcomm2]
  simp only [diagE, smul_add, Finset.sum_add_distrib, smul_neg]
  rw [hrho, two_smul ℂ (∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x)]
  abel

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rhoC_mul_sign_sum (ε : Fin n → Bool) (g : Bool → ℝ) :
    ∑ a, rhoC ε a * g (ε a) = 0 := by
  have hT : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then g (ε a) else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    by_cases h : b < a ∧ ε a = ε b
    · rw [if_pos h, if_pos ⟨h.1, h.2.symm⟩, h.2]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.symm⟩)]
  have e : ∀ a, rhoC ε a * g (ε a) = (∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) -
      ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0)) / 2 := by
    intro a
    unfold rhoC
    rw [natCast_card_filter, natCast_card_filter]
    have e1 : ∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if a < b ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    have e2 : ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if b < a ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    rw [e1, e2]; ring
  simp only [e]
  rw [← sum_div, sum_sub_distrib, hT, sub_self, zero_div]

theorem card_same_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 +
      (univ.filter fun b => a < b ∧ ε b = ε a).card := by
  rw [card_filter, card_filter, card_filter,
    show (1:ℕ) = ∑ b : Fin n, if b = a then 1 else 0 by simp, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b a with h | rfl | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp
  · simp [h, h.ne', not_lt_of_gt h]

theorem card_same_eq (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = if ε a then pOf ε else qOf ε := by
  cases h : ε a <;> simp [pOf, qOf]

theorem carU_pOf_add_qOf (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [card_filter, card_filter, ← sum_add_distrib]
  have : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [this]

def carUPos (ε : Fin n → Bool) (a : Fin n) : ℕ :=
  (if ε a then 0 else pOf ε) + (univ.filter fun b => b < a ∧ ε b = ε a).card

theorem carUPos_lt (ε : Fin n → Bool) (a : Fin n) : carUPos ε a < n := by
  have h1 := card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 := carU_pOf_add_qOf ε
  unfold carUPos
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> omega

theorem carUPos_injective (ε : Fin n → Bool) : Function.Injective (carUPos ε) := by
  have key : ∀ a a' : Fin n, a < a' → ε a = ε a' → carUPos ε a < carUPos ε a' := by
    intro a a' hlt he
    unfold carUPos
    rw [he]
    have hs : (univ.filter fun b => b < a ∧ ε b = ε a') ⊂ (univ.filter fun b => b < a' ∧ ε b = ε a') := by
      rw [ssubset_iff_of_subset]
      · exact ⟨a, by simp [hlt, he], by simp⟩
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact ⟨hb.1.trans hlt, hb.2⟩
    have := card_lt_card hs
    omega
  have key2 : ∀ a a' : Fin n, ε a = true → ε a' = false → carUPos ε a < carUPos ε a' := by
    intro a a' ha ha'
    have h1 := card_same_split ε a
    have h2 := card_same_eq ε a
    unfold carUPos
    simp only [ha, ha', Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    omega
  intro a a' hq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · by_cases he : ε a = ε a'
    · exact (key a a' h he).ne hq
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq
  · by_cases he : ε a' = ε a
    · exact (key a' a h he).ne hq.symm
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq

theorem rhoC_add_rhoHol_eq (ε : Fin n → Bool) (a : Fin n) :
    (rhoC ε + rhoHol ε) a = ((n : ℝ) - 1) / 2 - (carUPos ε a : ℝ) := by
  have h1 : ((univ.filter fun b => ε b = ε a).card : ℝ) =
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 +
        ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := by
    exact_mod_cast card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 : (pOf ε : ℝ) + (qOf ε : ℝ) = n := by exact_mod_cast carU_pOf_add_qOf ε
  simp only [Pi.add_apply, rhoC, rhoHol, carUPos]
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> rw [h2] at h1 <;> push_cast <;>
    linarith

theorem carU_nsq_add (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  unfold nsq dot
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring

theorem dot_rhoC_rhoHol (ε : Fin n → Bool) : dot (rhoC ε) (rhoHol ε) = 0 :=
  rhoC_mul_sign_sum ε (fun t => if t then (qOf ε : ℝ) / 2 else -(pOf ε : ℝ) / 2)

theorem nsq_rho_split (ε : Fin n → Bool) : nsq (rho n) = nsq (rhoC ε) + nsq (rhoHol ε) := by
  let σ : Fin n → Fin n := fun a => ⟨carUPos ε a, carUPos_lt ε a⟩
  have hinj : Function.Injective σ := fun a a' h => carUPos_injective ε (congrArg Fin.val h)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  have hval : ∀ a, (rhoC ε + rhoHol ε) a = rho n (σ a) := fun a => rhoC_add_rhoHol_eq ε a
  have hs : nsq (rhoC ε + rhoHol ε) = nsq (rho n) := by
    unfold nsq dot
    simp only [hval]
    exact (Equiv.ofBijective σ hbij).sum_comp (fun b => rho n b * rho n b)
  rw [← hs, carU_nsq_add, dot_rhoC_rhoHol]; ring

section Unitary
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]




end Unitary

section Value
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pair_apply_khw {E : Fin n → Fin n → Module.End ℂ W} {μ : Fin n → ℝ} {v : W} {a b : Fin n}
    (hc : E a b * E b a - E b a * E a b = E a a - E b b) (hd : ∀ a, E a a v = (μ a : ℂ) • v)
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by
  unfold hwTerm
  rcases lt_trichotomy a b with h | rfl | h
  · have hc' : E a b * E b a = E b a * E a b + (E a a - E b b) := by
      rw [← hc]; abel
    rw [hc']
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, hab h, map_zero,
      hd, zero_add, if_neg h.ne, if_pos h]
    push_cast
    rw [sub_smul]
  · simp only [Module.End.mul_apply, hd, map_smul, smul_smul, if_true]
    push_cast; ring_nf
  · simp [Module.End.mul_apply, hba h, h.ne', not_lt_of_gt h]

theorem casimirK_khwVec_compact (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ W}
    (hE : ∀ a b, ε a = ε b → E a b * E b a - E b a * E a b = E a a - E b b)
    {μ : Fin n → ℝ} {v : W} (hv : IsKHWVec ε E μ v) :
    casimirK ε E v = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • v := by
  have hsum : casimirK ε E v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), hwTerm μ a b : ℝ) : ℂ) • v := by
    unfold casimirK
    simp only [LinearMap.sum_apply]
    push_cast
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact pair_apply_khw (hE a b hb.symm) hv.1 (fun h => hv.2 a b h hb.symm) (fun h => hv.2 b a h hb)
  rw [hsum]
  congr 3
  exact sum_hwTerm (fun a b : Fin n => ε b = ε a) (fun _ => rfl) (fun a b h => h.symm) μ (rhoC ε)
    (fun a => by unfold rhoC; ring)

theorem E_comm_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (a b c d : Fin n) : E a b * sgE ε cp cm c d = sgE ε cp cm c d * E a b := by
  have h1 : ∀ i j k l, E a b * (cp i j * cm k l) = (cp i j * cm k l) * E a b := by
    intro i j k l
    rw [← mul_assoc, (hEC a b i j).1, mul_assoc, (hEC a b k l).2, mul_assoc]
  unfold sgE
  split_ifs
  · rw [mul_sum, sum_mul]; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · rw [mul_neg, neg_mul, mul_sum, sum_mul]; congr 1; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · simp

theorem diagE_compact {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (h : ε a = ε b) :
    diagE ε E cp cm a b * diagE ε E cp cm b a - diagE ε E cp cm b a * diagE ε E cp cm a b =
      diagE ε E cp cm a a - diagE ε E cp cm b b := by
  have e1 := hE a b b a
  have e2 := sgE_comm hC ε a b b a h h.symm
  simp only [if_true] at e1 e2
  rw [sub_eq_iff_eq_add] at e1 e2
  unfold diagE
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, E_comm_sgE hEC ε a b b a,
    E_comm_sgE hEC ε b a a b, e1, e2]
  abel

theorem khw_real_identity (ε : Fin n → Bool) (δ : Fin n → ℝ) :
    nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) =
      nsq (δ + rhoC ε) - nsq (rho n) := by
  rw [nsq_rho_split ε]
  have h0 := dot_rhoC_rhoHol ε
  have : nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) -
      (nsq (δ + rhoC ε) - (nsq (rhoC ε) + nsq (rhoHol ε))) = 2 * dot (rhoC ε) (rhoHol ε) := by
    unfold nsq dot
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply]; ring
  rw [h0] at this
  linarith

theorem two_D_sq_khw {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) {δ : Fin n → ℝ} {v : W}
    (hv : IsKHWVec ε (diagE ε E cp cm) (δ + rhoHol ε) v) {c : ℂ} (hc : casimir E v = c • v) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) v =
      (((nsq (δ + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - c) • v := by
  have hK := casimirK_khwVec_compact ε (diagE_compact hE hC hEC ε) hv
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε E cp cm a a v =
      ((dot (rhoHol ε) (δ + rhoHol ε) : ℝ) : ℂ) • v := by
    simp only [hv.1, smul_smul, ← sum_smul]
    congr 1
    unfold dot
    push_cast
    rfl
  rw [← LinearMap.smul_apply, two_D_sq hE hC hEC ε]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hc, hK, hs]
  rw [← khw_real_identity ε δ]
  simp only [smul_smul, sub_smul]
  push_cast
  simp only [sub_smul, mul_smul]
  abel

end Value

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

section Gen

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem fockT_cm_cp {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) {ε : Fin n → Bool}
    {j b u v : Fin n} (hjb : ¬(ε j = true ∧ ε b = false)) (huv : ε u = true ∧ ε v = false) (y : W) :
    cm j b (cp u v y) = -(cp u v (cm j b y)) := by
  have h3 := (hC j b u v).2.2
  have hne : ¬(j = u ∧ b = v) := by
    rintro ⟨rfl, rfl⟩
    exact hjb huv
  rw [if_neg hne] at h3
  have h := LinearMap.congr_fun h3 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_cm_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (j b w z : Fin n) (y : W) :
    cm j b (cm w z y) = -(cm w z (cm j b y)) := by
  have h := LinearMap.congr_fun (hC j b w z).2.1 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_stable_gen {E cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (hK : CommutesCAR E cp cm) (ε : Fin n → Bool) {j b : Fin n} (hjb : ¬(ε j = true ∧ ε b = false))
    {x : W} (hx : ∀ j b, ¬(ε j = true ∧ ε b = false) → cm j b x = 0) :
    (∀ a c, cm j b (E a c x) = 0) ∧ (∀ a c, cm j b (diagE ε E cp cm a c x) = 0) ∧
      cm j b (dOp ε E cp x) = 0 ∧ cm j b (dOp' ε E cm x) = 0 := by
  have hEc : ∀ a c y, cm j b (E a c y) = E a c (cm j b y) := fun a c y => by
    have h := LinearMap.congr_fun (hK a c j b).2 y
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hx0 := hx j b hjb
  have hE0 : ∀ a c, cm j b (E a c x) = 0 := fun a c => by rw [hEc, hx0, map_zero]
  have hcpcm : ∀ u v w z, ε u = true ∧ ε v = false → cm j b (cp u v (cm w z x)) = 0 := by
    intro u v w z huv
    rw [fockT_cm_cp hC hjb huv, fockT_cm_cm hC, hx0]
    simp
  refine ⟨hE0, fun a c => ?_, ?_, ?_⟩
  · simp only [diagE, LinearMap.add_apply, map_add, hE0, zero_add, sgE]
    split_ifs with h1 h2
    · simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply]
      refine Finset.sum_eq_zero fun y hy => hcpcm _ _ _ _ ⟨h1.1, ?_⟩
      simpa [minusIdx] using hy
    · simp only [LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Module.End.mul_apply]
      refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i hi => hcpcm _ _ _ _ ⟨?_, h2.2⟩)
      simpa [plusIdx] using hi
    · simp
  · simp only [dOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
    rw [hEc, fockT_cm_cp hC hjb ⟨by simpa [plusIdx] using hi, by simpa [minusIdx] using ha⟩, hx0]
    simp
  · simp only [dOp', LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Module.End.mul_apply]
    refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_)
    rw [hEc, fockT_cm_cm hC, hx0]
    simp

theorem fockT_anti_sum {R : Type*} [Ring R] {ι κ : Type*} (s : Finset ι) (t : Finset κ) (G : R)
    (A B : ι → κ → R) (hA : ∀ i k, G * A i k = A i k * G) (hB : ∀ i k, G * B i k = -(B i k * G)) :
    G * ∑ i ∈ s, ∑ k ∈ t, A i k * B i k = -((∑ i ∈ s, ∑ k ∈ t, A i k * B i k) * G) := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  calc G * (A i k * B i k) = A i k * (G * B i k) := by rw [← mul_assoc, hA, mul_assoc]
    _ = -(A i k * B i k * G) := by rw [hB, mul_neg, mul_assoc]

end Gen

section FockLemmas

variable {n : ℕ}

theorem fock_contractLeft_involute (d : Module.Dual ℂ (Fin n × Fin n → ℂ)) (x : Fock n) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x m hx =>
    simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg, CliffordAlgebra.contractLeft_ι_mul,
      hx, map_sub, map_smul, mul_neg]

theorem fock_inv_sq :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap *
      (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap = 1 :=
  LinearMap.ext fun x => CliffordAlgebra.involute_involute x

theorem fock_inv_cp (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cpFock i a =
      -(cpFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cpFock, CliffordAlgebra.involute_ι]

theorem fock_inv_cm (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cmFock i a =
      -(cmFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cmFock, fock_contractLeft_involute]

end FockLemmas

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

def eT (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map (E a b) LinearMap.id

def cpT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cpFock i a)

def cmT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cmFock i a)

def gradT : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map LinearMap.id (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap

def physicalSubspace (ε : Fin n → Bool) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  ⨅ i : Fin n, ⨅ a : Fin n, ⨅ (_ : ¬ (ε i = true ∧ ε a = false)), LinearMap.ker (cmT (N := N) i a)

def tensFock (V : Submodule ℂ N) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  LinearMap.range (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))

theorem gradT_eq : gradT (N := N) (n := n) =
    Module.End.lTensorAlgHom ℂ (Fock n) N (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap := rfl

theorem mem_physicalSubspace_iff (ε : Fin n → Bool) (x : TensorProduct ℂ N (Fock n)) :
    x ∈ physicalSubspace (N := N) ε ↔ ∀ j b, ¬(ε j = true ∧ ε b = false) → cmT j b x = 0 := by
  simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker]

theorem gradT_cpT (i a : Fin n) : gradT (N := N) * cpT i a = -(cpT i a * gradT) := by
  have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) (fock_inv_cp (n := n) i a)
  simp only [map_neg, map_mul] at h
  exact h

theorem gradT_cmT (i a : Fin n) : gradT (N := N) * cmT i a = -(cmT i a * gradT) := by
  have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) (fock_inv_cm (n := n) i a)
  simp only [map_neg, map_mul] at h
  exact h

theorem eT_gradT (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) : eT E a b * gradT = gradT * eT E a b :=
  TensorProduct.ext' fun x y => by simp [eT, gradT, TensorProduct.map_tmul]

theorem eT_isGlRep {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) : IsGlRep (eT (n := n) E) := by
  intro a b c d
  have h := congrArg (Module.End.rTensorAlgHom ℂ N (Fock n)) (hE a b c d)
  rw [map_sub, map_sub, map_mul, map_mul] at h
  refine h.trans ?_
  congr 1 <;> split_ifs <;> first | rfl | simp

theorem cpT_cmT_isCAR : IsCAR (cpT (N := N) (n := n)) cmT := by
  intro i a j b
  obtain ⟨h1, h2, h3⟩ := isCAR_fock (n := n) i a j b
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h1
    simp only [map_add, map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h2
    simp only [map_add, map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h3
    rw [map_add, map_mul, map_mul] at h
    refine h.trans ?_
    split_ifs <;> simp

theorem eT_commutesCAR (E : Fin n → Fin n → Module.End ℂ N) : CommutesCAR (eT E) cpT cmT := by
  intro a b i j
  refine ⟨TensorProduct.ext' fun x y => ?_, TensorProduct.ext' fun x y => ?_⟩ <;>
    simp [eT, cpT, cmT, TensorProduct.map_tmul]

theorem physSub_stable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, eT E a b x ∈ physicalSubspace ε) ∧
      (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, diagE ε (eT E) cpT cmT a b x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp ε (eT E) cpT x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp' ε (eT E) cmT x ∈ physicalSubspace ε) ∧
      ∀ x ∈ physicalSubspace (N := N) ε, gradT x ∈ physicalSubspace ε := by
  have hC := cpT_cmT_isCAR (N := N) (n := n)
  have hK := eT_commutesCAR (N := N) E
  refine ⟨fun a c x hx => ?_, fun a c x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rw [mem_physicalSubspace_iff] at hx ⊢ <;> intro j b hjb
  · exact (fockT_stable_gen hC hK ε hjb hx).1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.1
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.2
  · have h := LinearMap.congr_fun (gradT_cmT (N := N) j b) x
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
    rw [← neg_neg (cmT j b (gradT x)), ← h, hx j b hjb, map_zero, neg_zero]

theorem gradT_props (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    gradT (N := N) (n := n) * gradT = 1 ∧ gradT * dOp ε (eT E) cpT = -(dOp ε (eT E) cpT * gradT) ∧
      gradT * dOp' ε (eT E) cmT = -(dOp' ε (eT E) cmT * gradT) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gradT_eq, ← map_mul, fock_inv_sq, map_one]
  · exact fockT_anti_sum _ _ _ (fun i a => eT E a i) (fun i a => cpT i a) (fun i a => (eT_gradT E a i).symm)
      (fun i a => gradT_cpT i a)
  · simp only [dOp', mul_neg, neg_mul]
    rw [fockT_anti_sum _ _ _ (fun i a => eT E i a) (fun i a => cmT i a) (fun i a => (eT_gradT E i a).symm)
      (fun i a => gradT_cmT i a)]

end ReciprocityTheory.ChartRestriction.DS
end
end
