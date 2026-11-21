import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD Formalism.BasicNotions Formalism.MainNotions.G

theorem card_cells_eq_sum_rowLen (α : YoungDiagram) (n : ℕ) (h : ∀ r, n ≤ r → α.rowLen r = 0) :
    α.cells.card = ∑ r ∈ Finset.range n, α.rowLen r := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.range n)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [YoungDiagram.rowLen_eq_card]
    first
      | rfl
      | (simp only [YoungDiagram.row]; congr 1)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_range] at hx ⊢
    by_contra hc
    have h0 := h x.1 (not_lt.mp hc)
    have hx' : (x.1, x.2) ∈ α := hx
    rw [YoungDiagram.mem_iff_lt_rowLen] at hx'
    omega

theorem cPr_le_ctD (D : D7) (u : D.what₂.Word) (i : ℕ) (nu : Pl D → YoungDiagram)
    (hrow : ∀ z r, (((nu z).rowLen r : ℕ) : ℝ) =
      if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0)
    (hN : 2 ≤ D.R.N i) (t : HH D) :
    (cPr (nu (false, t)) (nu (true, t)) : ℝ) ≤ ctD D u (i + 1) t := by
  have hN0 : 0 < D.R.N i := by omega
  have hN1 : 1 < D.R.N i := by omega

  have hr : ∀ z r, r < D.R.N i → DV.nuRow D u (i + 1) (tauPl D z) r = ((nu z).rowLen r : ℝ) := by
    intro z r hr'
    rw [hrow z r, if_pos hr']
  have hz : ∀ z r, D.R.N i ≤ r → (nu z).rowLen r = 0 := by
    intro z r hr'
    have hz0 := hrow z r
    rw [if_neg (by omega)] at hz0
    exact_mod_cast hz0
  have hsum := card_cells_eq_sum_rowLen (nu (false, t)) (D.R.N i) (hz _)
  have habs : nuAbs D u (i + 1) (tauPl D (false, t)) = ((nu (false, t)).cells.card : ℝ) := by
    rw [hsum]
    unfold nuAbs
    rw [Nat.add_sub_cancel]
    push_cast
    refine Finset.sum_congr rfl fun r hr' => ?_
    exact hr _ r (Finset.mem_range.mp hr')
  have h0le : (nu (false, t)).rowLen 0 ≤ (nu (false, t)).cells.card := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun r => (nu (false, t)).rowLen r)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hN0)
  unfold cPr ctD
  rw [habs, hr (false, t) 0 hN0, hr (false, t) 1 hN1, hr (true, t) 0 hN0]
  push_cast [Nat.cast_sub h0le]
  have hm1 := min_le_left ((nu (false, t)).rowLen 0 : ℝ) ((nu (true, t)).rowLen 0 : ℝ)
  have hm2 := min_le_right ((nu (false, t)).rowLen 0 : ℝ) ((nu (true, t)).rowLen 0 : ℝ)
  have ha1 : (0 : ℝ) ≤ ((nu (false, t)).rowLen 1 : ℝ) := Nat.cast_nonneg _
  split_ifs <;> linarith

theorem entAtD_of_core (h : CoreBound) : PI.EntAtD.EntAtD := by
  unfold PI.EntAtD.EntAtD
  intro D Dx nu hrow hcol Th hTh u μ w hLF hram i hi L L'
  have hS := hTh u μ w hLF hram i hi L L'
  have hc := h (HH D) (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (nu u i)
    (Th u μ w i L L') hS
  have hN : 2 ≤ D.R.N i := by
    show 2 ≤ D.R.k + i * (D.R.t + 1)
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    exact le_trans (by omega : 2 ≤ D.R.k) (Nat.le_add_right _ _)

  have hle : ∑ t : HH D, (cPr (nu u i (false, t)) (nu u i (true, t)) : ℝ) ≤
      ∑ t : HH D, ctD D u (i + 1) t :=
    Finset.sum_le_sum fun t _ => cPr_le_ctD D u i (nu u i) (hrow u i hi) hN t
  have hp : (1 : ℝ) ≤ (D.what₂.places.resChar w : ℝ) := by
    have hpr : (D.what₂.places.resChar w).Prime := Fact.out
    exact_mod_cast hpr.one_lt.le
  unfold KvalGe at hc ⊢
  intro I m
  refine (hc I m).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le hp
  linarith

end PI.EntAtD.W
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem coreTerm_le {H : Type} [Fintype H] (p : ℕ) [Fact p.Prime] (S : ℂ_[p]) (ut : H → ℂ_[p])
    (hS : ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2)) (hut : ∀ t, ‖ut t‖ ≤ 1) (X : ℂ_[p]) (hX : ‖X‖ ≤ 1) (A : ℤ)
    (n c : H → ℕ) (hn : ∀ t, n t ≤ c t) :
    ‖X * (∏ t : H, (-(S * ut t)) ^ n t) * ((A : ℤ) : ℂ_[p])‖ ≤
      (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hp0.le _
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hp1 (by norm_num)
  have hA : ‖((A : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one ℂ_[p] A
  have h2 : ∏ t : H, ‖(-(S * ut t)) ^ n t‖ ≤ (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) := by
    calc ∏ t : H, ‖(-(S * ut t)) ^ n t‖ ≤ ∏ t : H, ((p : ℝ) ^ ((1 : ℝ) / 2)) ^ c t := by
          apply Finset.prod_le_prod (fun t _ => norm_nonneg _)
          intro t _
          rw [norm_pow, norm_neg, norm_mul]
          calc (‖S‖ * ‖ut t‖) ^ n t ≤ ((p : ℝ) ^ ((1 : ℝ) / 2)) ^ n t := by
                apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                calc ‖S‖ * ‖ut t‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) * 1 :=
                      mul_le_mul hS (hut t) (norm_nonneg _) hq0
                  _ = _ := mul_one _
            _ ≤ _ := pow_le_pow_right₀ hq1 (hn t)
      _ = _ := by
          rw [Finset.sum_div, Real.rpow_sum_of_pos hp0]
          refine Finset.prod_congr rfl (fun t _ => ?_)
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
          congr 1
          ring
  rw [norm_mul, norm_mul, norm_prod]
  calc ‖X‖ * (∏ t : H, ‖(-(S * ut t)) ^ n t‖) * ‖((A : ℤ) : ℂ_[p])‖
      ≤ 1 * (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) * 1 := by
        apply mul_le_mul (mul_le_mul hX h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
          hA (norm_nonneg _)
        exact mul_nonneg zero_le_one (Real.rpow_nonneg hp0.le _)
    _ = _ := by ring

theorem core_of (hE : PExpand) (hV : PVanish) : CoreBound := by
  intro H _ _ N0 N1 p _ nu Th hTh I m
  obtain ⟨S, hS, ut, hut, sg, hsg, rfl⟩ := hTh
  rw [hE H N0 N1 p S ut sg (Gxz N0 N1 nu I) m, neg_neg]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hB0 : (0 : ℝ) ≤ (p : ℝ) ^ ((∑ t : H, (cPr (nu (false, t)) (nu (true, t)) : ℝ)) / 2) :=
    Real.rpow_nonneg hp0.le _
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun κ2 _ => ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun n _ => ?_)
  by_cases hn : ∃ t, cPr (nu (false, t)) (nu (true, t)) < n t
  · obtain ⟨t, ht⟩ := hn
    rw [hV H N0 N1 nu I m κ2 n t ht]
    simpa using hB0
  · simp only [not_exists, not_lt] at hn
    exact coreTerm_le p S ut hS hut _ (hsg κ2) _ n (fun t => cPr (nu (false, t)) (nu (true, t))) hn

end PI.EntAtD.W
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem fprod_split_cast {H : Type} {N0 N1 p : ℕ} [Fact p.Prime] (κ κ2 : ZV H N0 N1 →₀ ℕ) (h : κ2 ≤ κ) :
    (κ.prod fun _ k => (k.factorial : ℂ_[p])) =
      ((binomF κ κ2 : ℕ) : ℂ_[p]) * ((κ - κ2).prod fun _ k => (k.factorial : ℂ_[p])) *
        (κ2.prod fun _ k => (k.factorial : ℂ_[p])) := by
  classical
  have hs1 : (κ - κ2).support ⊆ κ.support := by
    intro v hv
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hv
    rw [Finsupp.mem_support_iff]
    omega
  have hs2 : κ2.support ⊆ κ.support := by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv ⊢
    have := h v
    omega
  rw [Finsupp.prod_of_support_subset _ hs1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hs2 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset κ subset_rfl _ (fun _ _ => by simp)]
  simp only [binomF]
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.tsub_apply, mul_right_comm]
  exact_mod_cast (Nat.choose_mul_factorial_mul_factorial (h v)).symm

theorem fcoeff_mul {H : Type} [DecidableEq H] {N0 N1 p : ℕ} [Fact p.Prime] (E sg : MvPowerSeries (ZV H N0 N1) ℂ_[p])
    (κ : ZV H N0 N1 →₀ ℕ) :
    (κ.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ (E * sg) =
      ∑ κ2 ∈ Finset.Iic κ, ((binomF κ κ2 : ℕ) : ℂ_[p]) *
        (((κ - κ2).prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff (κ - κ2) E) *
        ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) := by
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_nbij' (fun x => x.2) (fun κ2 => (κ - κ2, κ2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp at hx
    simp only [Finset.mem_coe, Finset.mem_Iic]
    rw [← hx]
    exact le_add_self
  · intro κ2 hκ2
    simp only [Finset.mem_coe, Finset.mem_Iic] at hκ2
    simpa using tsub_add_cancel_of_le hκ2
  · intro x hx
    simp at hx
    refine Prod.ext ?_ rfl
    show κ - x.2 = x.1
    rw [← hx, add_tsub_cancel_right]
  · intro κ2 _
    rfl
  · intro x hx
    simp at hx
    have hle : x.2 ≤ κ := by
      rw [← hx]
      exact le_add_self
    have h1 : κ - x.2 = x.1 := by
      rw [← hx, add_tsub_cancel_right]
    rw [fprod_split_cast κ x.2 hle, h1]
    ring

theorem prof_le_totalDegree {H : Type} {N0 N1 : ℕ} (P : PolyXZ H N0 N1) (μ : XZ (Bool × H) N0 N1 →₀ ℕ)
    (hμ : μ ∈ P.support) (κ2 : ZV H N0 N1 →₀ ℕ) (t : H) :
    ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b) ≤ P.totalDegree := by
  classical
  calc ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b)
      ≤ ∑ a : Fin N0, ∑ b : Fin N1, μ (Sum.inr ((true, t), a, b)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [Finsupp.tsub_apply]
        exact tsub_le_self.trans (by
          first
          | exact le_of_eq rfl
          | exact (Finsupp.snd_sumFinsuppEquivProdFinsupp _ _).le)
    _ = ∑ x ∈ (Finset.univ : Finset (Fin N0 × Fin N1)).image
          (fun ab => (Sum.inr ((true, t), ab.1, ab.2) : XZ (Bool × H) N0 N1)), μ x := by
        rw [Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h), Fintype.sum_prod_type]
    _ ≤ ∑ x ∈ μ.support, μ x :=
        Finset.sum_le_sum_of_ne_zero fun x _ hx => Finsupp.mem_support_iff.2 hx
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hμ

theorem expand_gen {H : Type} [Fintype H] [DecidableEq H] {N0 N1 p : ℕ} [Fact p.Prime] (S : ℂ_[p])
    (ut : H → ℂ_[p]) (E sg : MvPowerSeries (ZV H N0 N1) ℂ_[p])
    (hE : ∀ κ : ZV H N0 N1 →₀ ℕ, (κ.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ E =
      if ∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b) then
        ∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          ((κ ((true, t), a, b)).factorial : ℂ_[p]) * (-(S * ut t)) ^ κ ((true, t), a, b)
      else 0)
    (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ) :
    MvPolynomial.coeff m (applyAt0 N0 N1 p (E * sg) P) =
      ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)),
        ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)),
          ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) *
            (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p]) := by
  classical
  let T : (XZ (Bool × H) N0 N1 →₀ ℕ) → (ZV H N0 N1 →₀ ℕ) → ℂ_[p] := fun μ κ2 =>
    if xpart μ = m ∧ κ2 ≤ zpart μ ∧
        (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)) then
      ((MvPolynomial.coeff μ P : ℤ) : ℂ_[p]) * ((binomF (zpart μ) κ2 : ℕ) : ℂ_[p]) *
        (∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          (((zpart μ - κ2) ((true, t), a, b)).factorial : ℂ_[p]) *
            (-(S * ut t)) ^ (zpart μ - κ2) ((true, t), a, b)) *
        ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg)
    else 0
  have hL : MvPolynomial.coeff m (applyAt0 N0 N1 p (E * sg) P) =
      ∑ μ ∈ P.support, ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), T μ κ2 := by
    simp only [applyAt0, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    by_cases hx : xpart μ = m
    · rw [if_pos hx, mul_assoc, fcoeff_mul, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_biUnion_of_mem (fun μ => Finset.Iic (zpart μ)) hμ)
        (fun κ2 _ hn => by
          simp only [T]
          rw [if_neg]
          exact fun h => hn (Finset.mem_Iic.2 h.2.1))]
      refine Finset.sum_congr rfl fun κ2 hκ2 => ?_
      have hle : κ2 ≤ zpart μ := Finset.mem_Iic.1 hκ2
      rw [hE]
      simp only [T]
      by_cases hb : ∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)
      · rw [if_pos hb, if_pos ⟨hx, hle, hb⟩]
        ring
      · rw [if_neg hb, if_neg (fun h => hb h.2.2)]
        ring
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun κ2 _ => ?_
      simp only [T]
      rw [if_neg]
      exact fun h => hx h.1
  have hR : (∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)),
        ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)),
          ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) *
            (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p])) =
      ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), ∑ μ ∈ P.support, T μ κ2 := by
    refine Finset.sum_congr rfl fun κ2 _ => ?_
    simp only [Acon, Int.cast_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    by_cases hQ : xpart μ = m ∧ κ2 ≤ zpart μ ∧
        (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b))
    · have hB : Bal N0 N1 (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b))
          (zpart μ - κ2) := And.intro hQ.2.2 fun t => rfl
      rw [Finset.sum_eq_single (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b))]
      · rw [if_pos ⟨hQ.1, hQ.2.1, hB⟩]
        simp only [T]
        rw [if_pos hQ]
        push_cast
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] <;> ring
      · intro n _ hn
        rw [if_neg, Int.cast_zero, mul_zero]
        rintro ⟨_, _, hB'⟩
        exact hn (funext fun t => (hB'.2 t).symm)
      · intro hn
        exfalso
        exact hn (Fintype.mem_piFinset.2 fun t =>
          Finset.mem_range.2 (Nat.lt_succ_of_le (prof_le_totalDegree P μ hμ κ2 t)))
    · simp only [T]
      rw [if_neg hQ]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [if_neg, Int.cast_zero, mul_zero]
      rintro ⟨h1, h2, hB'⟩
      exact hQ ⟨h1, h2, hB'.1⟩
  rw [hL, hR, Finset.sum_comm]

theorem expand_of (hX : PExpCoeff) : PExpand := by
  intro H _ _ N0 N1 p _ S ut sg P m
  exact expand_gen S ut _ sg (fun κ => hX H N0 N1 p S ut κ) P m

end PI.EntAtD.W
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem list_prod_eq_mul_of_mem {M : Type} [Monoid M] (x : M) :
    ∀ l : List M, (∀ y ∈ l, Commute y x) → x ∈ l → ∃ r : M, l.prod = r * x
  | [], _, hx => absurd hx (List.not_mem_nil)
  | a :: l, hc, hx => by
    rcases List.mem_cons.1 hx with h | h
    · subst h
      refine ⟨l.prod, ?_⟩
      rw [List.prod_cons]
      exact (Commute.list_prod_left _ _ fun y hy => hc y (List.mem_cons_of_mem _ hy)).eq.symm
    · obtain ⟨r, hr⟩ := list_prod_eq_mul_of_mem x l (fun y hy => hc y (List.mem_cons_of_mem _ hy)) h
      exact ⟨a * r, by rw [List.prod_cons, hr, mul_assoc]⟩

theorem vanish_of (hB : PBridge) (hC : PLapComm) (hZ : PLapZero) : PVanish := by
  intro H _ _ N0 N1 nu I m κ2 n t ht
  have hzero : lapAll N0 N1 n (Gxz N0 N1 nu I) = 0 := by
    obtain ⟨r, hr⟩ := list_prod_eq_mul_of_mem (lapT (H := H) N0 N1 t ^ n t)
      ((Finset.univ : Finset H).toList.map fun t => lapT N0 N1 t ^ n t)
      (fun y hy => by
        obtain ⟨t', _, rfl⟩ := List.mem_map.1 hy
        exact (hC H N0 N1 t' t).pow_pow _ _)
      (List.mem_map.2 ⟨t, Finset.mem_toList.2 (Finset.mem_univ t), rfl⟩)
    unfold lapAll
    rw [hr, Module.End.mul_apply, hZ H N0 N1 nu I t (n t) ht, map_zero]
  have h := hB H N0 N1 (Gxz N0 N1 nu I) m κ2 n
  rw [hzero, MvPolynomial.coeff_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (Finset.prod_ne_zero_iff.2 fun t' _ => by exact_mod_cast (Nat.factorial_ne_zero (n t')))
  · exact h

end PI.EntAtD.W
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

section Ker

variable {A : Type} [CommRing A] (D : Derivation ℤ A A)

def heartKer : Subring A where
  carrier := {f | D f = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb, add_zero]
  zero_mem' := D.map_zero
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_neg, ha, neg_zero]

end Ker

private theorem derivation_prod_eq_zero_of_forall' {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Derivation.leibniz, h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), smul_zero, smul_zero, add_zero]

private theorem derivation_det_eq_zero_of_entries {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) {k : ℕ} (M : Matrix (Fin k) (Fin k) A) (h : ∀ i j, D (M i j) = 0) :
    D M.det = 0 := by
  rw [Matrix.det_apply, map_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_prod_eq_zero_of_forall' D _ _ (fun i _ => h _ _), smul_zero]

theorem heart_pderiv_minor {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (s s' : Lt) (hs : s ≠ s')
    (k : ℕ) (I : Fin k ↪o Fin N1) (a : Fin N0) (b : Fin N1) :
    MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) (minorXZ N0 N1 s k I) = 0 := by
  simp only [minorXZ]
  apply derivation_det_eq_zero_of_entries
  intro i j
  rw [Matrix.of_apply, map_sum]
  refine Finset.sum_eq_zero fun a0 _ => ?_
  rw [Derivation.leibniz, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
  simp [Pi.single_apply, hs, Ne.symm hs]

private theorem derivation_finset_sum_apply' {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (s : Finset ι) (D : ι → Derivation R A A) (x : A) : (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

theorem heart_dRow_zero {H : Type} {N0 N1 : ℕ} (t : H) (r : ℕ) (b : Fin N1) (f : PolyXZ H N0 N1)
    (h : ∀ a : Fin N0, MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, b)) f = 0) :
    dRow (N0 := N0) t r b f = 0 := by
  simp only [dRow]
  rw [derivation_finset_sum_apply']
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Derivation.smul_apply, h a, smul_zero]

theorem heart_sdeg_prod (hS : PSDegMul) {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A)
    {κ : Type} [DecidableEq κ] (s : Finset κ) (f : κ → A) (k : κ → ℕ) :
    (∀ i ∈ s, SDegD d (k i) (f i)) → SDegD d (∑ i ∈ s, k i) (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, Finset.prod_empty]
    intro j
    exact (d j).map_one_eq_zero
  · intro i s hi ih h
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact hS A ι d _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lapZero_of (hM : PMinorAff) (hS : PSDegMul) (hF : PLapForms) : PLapZero := by
  intro H _ inst N0 N1 nu I t n hn
  clear inst
  let P : Bool × H → PolyXZ H N0 N1 := fun s => ∏ c : Fin ((nu s).rowLen 0),
    minorXZ (Lt := Bool × H) N0 N1 s ((nu s).colLen c) (I s c)
  let R : PolyXZ H N0 N1 := ∏ s ∈ (Finset.univ.erase (false, t)).erase (true, t), P s
  have hne : (true, t) ≠ (false, t) := by simp
  have hmem : (true, t) ∈ Finset.univ.erase (false, t) := by simp
  have hG : Gxz N0 N1 nu I = P (false, t) * (P (true, t) * R) := by
    show (∏ s, P s) = _
    rw [← Finset.mul_prod_erase Finset.univ P (Finset.mem_univ (false, t)),
      ← Finset.mul_prod_erase (Finset.univ.erase (false, t)) P hmem]
  have hnoP : ∀ (s s' : Bool × H), s ≠ s' → ∀ (a : Fin N0) (b : Fin N1),
      MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) (P s) = 0 := by
    intro s s' hs a b
    apply derivation_prod_eq_zero_of_forall'
    intro c _
    convert heart_pderiv_minor N0 N1 s s' hs _ (I s c) a b
  have hnoR : ∀ (s' : Bool × H), s' = (false, t) ∨ s' = (true, t) → ∀ (a : Fin N0) (b : Fin N1),
      MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) R = 0 := by
    intro s' hs' a b
    apply derivation_prod_eq_zero_of_forall'
    intro s hs
    apply hnoP s s' _ a b
    rintro rfl
    rcases hs' with rfl | rfl
    · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hs) rfl
    · exact Finset.ne_of_mem_erase hs rfl
  have h1 : ∀ (a : Fin N0) (b : Fin N1), pd (Sum.inr ((false, t), a, b)) (P (true, t) * R) = 0 := by
    intro a b
    show MvPolynomial.pderiv (R := ℤ) (Sum.inr ((false, t), a, b)) (P (true, t) * R) = 0
    rw [Derivation.leibniz, hnoP (true, t) (false, t) hne a b, hnoR (false, t) (Or.inl rfl) a b,
      smul_zero, smul_zero, add_zero]
  have hR0 : SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) 0 R := by
    intro b
    exact heart_dRow_zero t 0 b R (fun a => hnoR (true, t) (Or.inr rfl) a b)
  have hmin : ∀ c : Fin ((nu (true, t)).rowLen 0), SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) 1
      (minorXZ (Lt := Bool × H) N0 N1 (true, t) ((nu (true, t)).colLen c) (I (true, t) c)) := by
    intro c j j'
    exact hM H N0 N1 t _ _ j' j
  have hPT0 := heart_sdeg_prod hS (fun b : Fin N1 => dRow (N0 := N0) t 0 b) Finset.univ _ (fun _ => 1)
    (fun c _ => hmin c)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hPT0
  have hPT : SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) ((nu (true, t)).rowLen 0) (P (true, t)) :=
    hPT0
  have h2 := hS _ _ _ _ _ _ 0 hPT hR0
  rw [hG]
  exact hF H N0 N1 (nu (false, t)) (I (false, t)) t (P (true, t) * R) ((nu (true, t)).rowLen 0) n h1 h2 hn

end PI.EntAtD.W
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem entAtD_of (hX : PExpCoeff) (hB : PBridge) (hC : PLapComm) (hM : PMinorAff) (hS : PSDegMul)
    (hF : PLapForms) : PI.EntAtD.EntAtD :=
  entAtD_of_core (core_of (expand_of hX) (vanish_of hB hC (lapZero_of hM hS hF)))

end PI.EntAtD.W
end
end
