import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.MainNotions.BridgeLemma Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.NGDict

section HpSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem le_mul_mul_rpow_neg_half_of_le_inv_sq {a b c q : ℝ} (hq : 0 < q) (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1)
    (c0 : 0 < c) (h : c ≤ (q ^ 2)⁻¹) : q ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  have hx : a * b * c ≤ (q ^ 2)⁻¹ := by
    calc a * b * c ≤ 1 * 1 * c := by gcongr
      _ = c := by ring
      _ ≤ _ := h
  have e : ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = q := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hq.le]
  calc q = ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) := e.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hx (by norm_num)

theorem ends_isUnit {l : ℕ} (hl : l ∈ P.ends) : IsUnit (P.Dm l) :=
  (((@Finset.mem_filter _ _ (Classical.decPred _) _ _).1 hl).2).2

theorem residue_le_height_nonprime (hOK : M.OK) (hR : P.RelG (theta M))
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) (hp : ¬ P.PrimeTo) : StepHp P := by
  obtain ⟨d, t, ht⟩ := hex
  have hG : P.Gv ≠ 0 := hR.2.2.1
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := ng_factors hOK hG ht
  have hq : (0 : ℝ) < qF F := by
    have := two_le_residue_card hOK
    exact_mod_cast (by omega : 0 < qF F)
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  have hm1 : ((-1 : F) ^ (r + 1)) ∈ 𝒪[F] := pow_mem (neg_mem (one_mem _)) _
  unfold StepHp FPair.Hp
  rcases hs : M.split with _ | g
  · have hnot : ¬ IsUnitO M P.Gv ∨ ∃ l ∈ P.ends, ¬ IsUnitO M (P.Dm l) := by
      by_contra hc
      push Not at hc
      exact hp ⟨hs, hc.1, hc.2⟩
    rcases hnot with hGn | ⟨l, hl, hDn⟩
    · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inr ?_)
      have hfix : M.L.cj P.Gv = P.Gv := by
        unfold FPair.Gv HermSp.Gdet HermSp.normE
        simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
        ring
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hdet : (H.gram P.MMgen).det = algebraMap F E ((-1) ^ (r + 1) * a) := by
        rw [gram_det_eq P hs, ← ha, map_mul, map_pow, map_neg, map_one]
      have hmem : (H.gram P.MMgen).det ∈ M.L.O := by
        rw [← ng_term_gram ht]
        exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
      have haO : (-1) ^ (r + 1) * a ∈ 𝒪[F] :=
        Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [← hdet]; exact hmem)
      have haO' : a ∈ 𝒪[F] := by
        have h2 := mul_mem hm1 haO
        have e : ((-1 : F) ^ (r + 1)) * ((-1) ^ (r + 1) * a) = a := by
          rw [← mul_assoc, ← mul_pow]; simp
        rwa [e] at h2
      have ha0 : (-1) ^ (r + 1) * a ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (fun h => hG ?_)
        rw [← ha, h, map_zero]
      rw [hdet]
      refine ng_modK_nonunit hOK ⟨_, haO⟩ ha0 (fun hu => hGn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : ((-1) ^ (r + 1) * a) * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨?_, algebraMap F E ((-1) ^ (r + 1) * (y : F)), ?_, ?_⟩
      · rw [← ha]; exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨a, haO'⟩
      · exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨_, mul_mem hm1 y.2⟩
      · rw [← ha, ← map_mul]
        have : a * ((-1) ^ (r + 1) * (y : F)) = ((-1) ^ (r + 1) * a) * (y : F) := by ring
        rw [this, hy', map_one]
    · have hlu : IsUnit (P.Dm l) := ends_isUnit hl
      have hfac : ∀ l' ∈ P.ends, 0 < M.modK (P.Dm l' * M.L.cj (P.Dm l')) ∧
          M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤ 1 := by
        intro l' hl'
        have hu := ends_isUnit hl'
        have h := ng_modK hOK (hu.mul (hu.map M.L.cj))
        exact ⟨h.1, h.2 (M.L.O.mul_mem (ng_term_Dm ht l')
          (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l')))⟩
      have hcl : ∏ l' ∈ P.ends, M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤
          M.modK (P.Dm l * M.L.cj (P.Dm l)) := by
        rw [← Finset.mul_prod_erase _ _ hl]
        have h1 : ∏ x ∈ P.ends.erase l, M.modK (P.Dm x * M.L.cj (P.Dm x)) ≤ 1 :=
          Finset.prod_le_one (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).1.le)
            (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).2)
        have h0 := (hfac l hl).1.le
        calc _ ≤ M.modK (P.Dm l * M.L.cj (P.Dm l)) * 1 := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := mul_one _
      refine le_mul_mul_rpow_neg_half_of_le_inv_sq hq a0 a1 b0 b1 c0 (le_trans hcl ?_)
      have hfix : M.L.cj (P.Dm l * M.L.cj (P.Dm l)) = P.Dm l * M.L.cj (P.Dm l) := by
        rw [map_mul, M.L.cj_cj, mul_comm]
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hxO : P.Dm l * M.L.cj (P.Dm l) ∈ M.L.O :=
        M.L.O.mul_mem (ng_term_Dm ht l) (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
      have haO : a ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [ha]; exact hxO)
      have hxu : IsUnit (P.Dm l * M.L.cj (P.Dm l)) := hlu.mul (hlu.map M.L.cj)
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [map_zero] at ha
        rw [← ha] at hxu
        exact not_isUnit_zero hxu
      rw [← ha]
      refine ng_modK_nonunit hOK ⟨a, haO⟩ ha0 (fun hu => hDn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : a * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨ng_term_Dm ht l, M.L.cj (P.Dm l) * algebraMap F E (y : F),
        M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
          (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L y), ?_⟩
      rw [← mul_assoc, ← ha, ← map_mul, hy', map_one]
  · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inl ?_)
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hθ]
    exact ng_modK_nonunit hOK g.q (fun h => g.q_irr.ne_zero (Subtype.ext h)) g.q_irr.not_isUnit

end HpSec

section GlueSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}





theorem massE_eq (R : Reps P) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1))
    (S : Term V M r → Prop) : massE R d S = ENNReal.ofReal (massS R d S) := by
  unfold massE massS
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => mu_nonneg _) (summable_sub R d hs S)]

theorem massS_le_finsum (R : Reps P) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1))
    (S : Term V M r → Prop) {ι : Type} (s : Finset ι) (Si : ι → Term V M r → Prop)
    (h : ∀ t ∈ R.RT d, S t → ∃ i ∈ s, Si i t) : massS R d S ≤ ∑ i ∈ s, massS R d (Si i) := by
  set f : Term V M r → ℝ := fun t => mu P t with hf
  have e : ∀ S' : Term V M r → Prop, massS R d S' = ∑' t, ({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f t :=
    fun S' => tsum_subtype ({t | t ∈ R.RT d ∧ S' t} : Set _) f
  have hsum : ∀ S' : Term V M r → Prop, Summable (({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f) := by
    intro S'
    rw [← summable_subtype_iff_indicator]
    exact summable_sub R d hs S'
  have hnn : ∀ (S' : Term V M r → Prop) t, 0 ≤ ({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f t :=
    fun S' t => Set.indicator_nonneg (fun _ _ => mu_nonneg _) t
  rw [e S]
  simp only [e]
  rw [← Summable.tsum_finsetSum (fun i _ => hsum _)]
  refine Summable.tsum_le_tsum (fun t => ?_) (hsum S) (summable_sum (fun i _ => hsum _))
  by_cases ht : t ∈ R.RT d ∧ S t
  · obtain ⟨i, hi, hSi⟩ := h t ht.1 ht.2
    rw [Set.indicator_of_mem (show t ∈ {t | t ∈ R.RT d ∧ S t} from ht)]
    calc f t = ({t | t ∈ R.RT d ∧ Si i t} : Set _).indicator f t :=
          (Set.indicator_of_mem (show t ∈ {t | t ∈ R.RT d ∧ Si i t} from ⟨ht.1, hSi⟩) f).symm
      _ ≤ ∑ j ∈ s, ({t | t ∈ R.RT d ∧ Si j t} : Set _).indicator f t :=
          Finset.single_le_sum (f := fun j => ({t | t ∈ R.RT d ∧ Si j t} : Set _).indicator f t)
            (fun j _ => hnn _ t) hi
  · rw [Set.indicator_of_notMem (show t ∉ {t | t ∈ R.RT d ∧ S t} from ht)]
    exact Finset.sum_nonneg (fun j _ => hnn _ t)

theorem massS_mono (R : Reps P) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1))
    {S S' : Term V M r → Prop} (h : ∀ t ∈ R.RT d, S t → S' t) : massS R d S ≤ massS R d S' := by
  have := massS_le_finsum R d hs S ({()} : Finset Unit) (fun _ => S')
    (fun t ht hS => ⟨(), Finset.mem_singleton_self _, h t ht hS⟩)
  simpa using this


theorem sum_wt_mul_massS_le_inv_pow_mul_total_mass {k : ℕ} {R : Reps P} {d0 : Datum P} (hC1 : MassBoundLevelSets k R d0) (hH : 1 ≤ P.Hp) (Ds : Finset R.RD)
    (off : ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅) (summ : ∀ d : R.RD, Summable (fun t : R.RT d.1 => mu P t.1))
    (β : ℕ) (hβ : 1 ≤ β) (S : Term V M r → Prop) (h : ∀ (d : Datum P), ∀ t ∈ R.RT d, S t → be H t = β) :
    ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 S ≤
      A1 P * ((β : ℝ) ^ (k - 1))⁻¹ * ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 := by
  have hA : 0 ≤ A1 P * ((β : ℝ) ^ (k - 1))⁻¹ := by
    unfold A1
    have : (0 : ℝ) ≤ P.Hp := by linarith
    positivity
  have hle : ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 S ≤
      ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => be H t = β) := by
    refine Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left ?_ (wt_nonneg _ _))
    exact massS_mono R d.1.1 (summ d.1) (fun t ht hS => h _ t ht hS)
  refine le_trans hle ?_
  have key := hC1 β hβ
  have e1 : ∑' d : R.RD, ENNReal.ofReal (Datum.wt d0 d.1) * massE R d.1 (fun t => be H t = β) =
      ENNReal.ofReal (∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => be H t = β)) := by
    rw [tsum_eq_sum (s := Ds) (fun d hd => by
        have e3 : massE R d.1 (fun t => be H t = β) = 0 := by
          unfold massE
          have e2 : IsEmpty {t // t ∈ R.RT d.1 ∧ be H t = β} :=
            ⟨fun t => (Set.ext_iff.1 (off d hd) t.1).1 t.2.1⟩
          rw [tsum_empty]
        rw [e3, mul_zero]),
      Finset.sum_coe_sort Ds (fun d : R.RD => Datum.wt d0 d.1 * massS R d.1 (fun t => be H t = β)),
      ENNReal.ofReal_sum_of_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (massS_nonneg _ _ _))]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [ENNReal.ofReal_mul (wt_nonneg _ _), massE_eq R d.1 (summ d) _]
  rw [e1, nn_eq R d0 Ds off summ, ← ENNReal.ofReal_mul hA] at key
  have hX : 0 ≤ ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (tsum_nonneg (fun _ => mu_nonneg _)))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hX)).1 key





theorem lev_bdd (t : Term V M r) (y : V) :
    BddAbove {n | ∃ i : Fin (r + 1), n = i.val + 1 ∧ OutAt t y i} :=
  ⟨r + 1, by rintro n ⟨i, rfl, _⟩; have := i.isLt; omega⟩

theorem lev_le (t : Term V M r) (y : V) : lev t y ≤ r + 1 := by
  unfold lev
  apply csSup_le'
  rintro n ⟨i, rfl, _⟩
  have := i.isLt
  omega

theorem le_lev {t : Term V M r} {y : V} {i : Fin (r + 1)} (h : OutAt t y i) : i.val + 1 ≤ lev t y :=
  le_csSup (lev_bdd t y) ⟨i, rfl, h⟩























end GlueSec






end Formalism.L2.SG.Pf
