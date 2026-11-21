import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

section
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
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.NGLocModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem sum_le_sumSq {P : FPair H r} (R : Reps P) (d0 : Datum P) (S : Term V M r → Prop) (Ds : Finset (Datum P))
    (hD : ∀ d ∈ Ds, d ∈ R.RD) :
    ∑ d ∈ Ds, ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2) ≤ sumSq R d0 S := by
  unfold sumSq
  rw [← Finset.sum_subtype_of_mem
    (fun d => ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2)) hD]
  exact ENNReal.sum_le_tsum _

theorem real_sum_le {P : FPair H r} (R : Reps P) (d0 : Datum P) (S : Term V M r → Prop) (Ds : Finset (Datum P))
    (hD : ∀ d ∈ Ds, d ∈ R.RD) {B : ENNReal} (hB : sumSq R d0 S ≤ B) (hBt : B ≠ ⊤) :
    ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d S‖ ^ 2 ≤ B.toReal := by
  have h1 := (sum_le_sumSq R d0 S Ds hD).trans hB
  have hfin : ∀ d ∈ Ds, ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2) ≠ ⊤ := fun d _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  calc ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d S‖ ^ 2
      ≤ ∑ d ∈ Ds, (ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2)).toReal := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = (∑ d ∈ Ds, ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2)).toReal :=
        (ENNReal.toReal_sum hfin).symm
    _ ≤ B.toReal := ENNReal.toReal_mono hBt h1

theorem ngAt_real (k C1 : ℕ) (hk : 2 * r + 5 ≤ k) {P : FPair H r} (hNG : NGAt k P (C1 : ℝ)) (R : Reps P)
    (d0 : Datum P) (Ds : Finset (Datum P)) (hD : ∀ d ∈ Ds, d ∈ R.RD) (hn : nn R d0 ≠ ⊤) (hHp : 0 ≤ P.Hp) :
    ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d (BBne (H := H))‖ ^ 2 ≤
        P.Hp ^ (C1 * (r + 1) ^ 2) * (((qF F : ℕ) : ℝ) ^ (k - 2 * r - 5))⁻¹ * (nn R d0).toReal ∧
      ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d (fun t => ¬ BBne (H := H) t)‖ ^ 2 ≤
        P.Hp ^ (C1 * (r + 1) ^ 2) * (nn R d0).toReal := by
  obtain ⟨h1, h2, -, -⟩ := hNG R d0
  have hq : (0 : ℝ) ≤ ((qF F : ℕ) : ℝ) := Nat.cast_nonneg _
  have eC : ((C1 : ℕ) : ℝ) * ((r : ℝ) + 1) ^ 2 = ((C1 * (r + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
  have hk' : ((k - 2 * r - 5 : ℕ) : ℝ) = (k : ℝ) - 2 * r - 5 := by
    have e1 : k - 2 * r - 5 + (2 * r + 5) = k := by omega
    have e2 := congrArg (Nat.cast (R := ℝ)) e1
    push_cast at e2
    linarith
  have eK : -((k : ℝ) - 2 * r - 5) = -((k - 2 * r - 5 : ℕ) : ℝ) := by rw [hk']
  rw [eC, Real.rpow_natCast] at h1 h2
  rw [eK, Real.rpow_neg hq, Real.rpow_natCast] at h1
  have hX1 : 0 ≤ P.Hp ^ (C1 * (r + 1) ^ 2) * (((qF F : ℕ) : ℝ) ^ (k - 2 * r - 5))⁻¹ :=
    mul_nonneg (pow_nonneg hHp _) (inv_nonneg.mpr (pow_nonneg hq _))
  have hX2 : 0 ≤ P.Hp ^ (C1 * (r + 1) ^ 2) := pow_nonneg hHp _
  constructor
  · have h3 := real_sum_le R d0 _ Ds hD h1 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hX1] at h3
  · have h3 := real_sum_le R d0 _ Ds hD h2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hX2] at h3

end Gen

section Fam

variable {D : D7}

structure LocFam (Z : LocDat D) (Cl Nu : Type) where
  P : Finset (PlF D)
  Om : Finset {p // p ∈ P}
  FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS
  R : ∀ p : PlF D, LocNG.Reps (FP p)
  d0 : ∀ p : PlF D, LocNG.Datum (FP p)
  Ds : ∀ p : PlF D, Finset (LocNG.Datum (FP p))
  ngenL : PlF D → ℝ
  V0 : ℝ
  rw : Cl → ℝ
  dat : Cl → Nu → Option (∀ p : {p // p ∈ P}, {d // d ∈ Ds p.1})

def LocFam.toL {Z : LocDat D} {Cl Nu : Type} (Fm : LocFam Z Cl Nu) : PN.LocalNG Cl Nu where
  P := {p // p ∈ Fm.P}
  Om := Fm.Om
  D p := {d // d ∈ Fm.Ds p.1}
  wt p d := LocNG.Datum.wt (Fm.d0 p.1) d.1
  aN p d := LocNG.amp (Fm.R p.1) d.1 (LocNG.BBne (H := locH Z p.1))
  aZ p d := LocNG.amp (Fm.R p.1) d.1 (fun t => ¬ LocNG.BBne (H := locH Z p.1) t)
  H p := (Fm.FP p.1).Hp
  nn p := (LocNG.nn (Fm.R p.1) (Fm.d0 p.1)).toReal
  ngen p := Fm.ngenL p.1
  q p := LocNG.qF (D.s.atP p.1).Fp
  V0 := Fm.V0
  rw := Fm.rw
  dat := Fm.dat

theorem ngAt_toL {Z : LocDat D} {Cl Nu : Type} (Fm : LocFam Z Cl Nu) (C1 : ℕ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ))
    (hD : ∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) (hn : ∀ p ∈ Fm.P, LocNG.nn (Fm.R p) (Fm.d0 p) ≠ ⊤)
    (hH : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp) : Fm.toL.NGAt C1 D.R.rS D.R.k := by
  unfold PN.LocalNG.NGAt
  refine ⟨fun p _ => ?_, ?_⟩
  · have h1 := (ngAt_real D.R.k C1 hk (hNG p.1 p.2) (Fm.R p.1) (Fm.d0 p.1) (Fm.Ds p.1) (hD p.1 p.2)
      (hn p.1 p.2) (hH p.1 p.2)).1
    rw [← Finset.sum_coe_sort (Fm.Ds p.1)] at h1
    exact h1
  · intro p
    have h1 := (ngAt_real D.R.k C1 hk (hNG p.1 p.2) (Fm.R p.1) (Fm.d0 p.1) (Fm.Ds p.1) (hD p.1 p.2)
      (hn p.1 p.2) (hH p.1 p.2)).2
    rw [← Finset.sum_coe_sort (Fm.Ds p.1)] at h1
    exact h1

def FamOK {Z : LocDat D} {τ : Type} {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (γ : PN.Pts D.host.E D.R.rS) (S : Finset (Cl × Nu)) (C0n : ℕ) (AAre : ℝ)
    (Fm : LocFam Z Cl Nu) : Prop :=
  (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta (Z.M p))) ∧
  (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Formalism.MainNotions.S.Loc.Term (Vp D p) (Z.M p) D.R.rS),
    LocNG.IsTermOver (Fm.FP p) d t) ∧
  (∀ p : {p // p ∈ Fm.P}, p ∈ Fm.Om ↔ ¬ (Fm.FP p.1).PrimeTo) ∧
  (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ p ∈ Fm.P, LocNG.nn (Fm.R p) (Fm.d0 p) ≠ ⊤) ∧
  0 ≤ Fm.V0 ∧ (∀ c, 0 ≤ Fm.rw c) ∧ Fm.toL.MassRatioAt C0n D.R.rS ∧ Fm.toL.Unfold ∧
  (∀ x ∈ S, N.a2 x.1 γ x.2 = Fm.toL.a2 x.1 x.2) ∧ N.Hh γ = Fm.toL.Htot ∧
  0 < Fm.toL.ngenTot ∧ Fm.toL.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN D.R.rS * N.n γ

def a2W {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (amp : (∀ p, L.D p) → ℂ) (c : Cl) (ν : Nu) : ℝ :=
  match L.dat c ν with
  | none => 0
  | some d => L.rw c * ‖amp d‖ ^ 2

theorem localAmplitudeSq_eq_weighted {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (c : Cl) (ν : Nu) : L.a2 c ν = a2W L L.ampNG c ν := rfl

def FamOKS {Z : LocDat D} {τ : Type} {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (γ : PN.Pts D.host.E D.R.rS) (S : Finset (Cl × Nu)) (C0n : ℕ) (AAre : ℝ)
    (amp : ∀ L : PN.LocalNG Cl Nu, (∀ p, L.D p) → ℂ) (Fm : LocFam Z Cl Nu) : Prop :=
  (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta (Z.M p))) ∧
  (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Formalism.MainNotions.S.Loc.Term (Vp D p) (Z.M p) D.R.rS),
    LocNG.IsTermOver (Fm.FP p) d t) ∧
  (∀ p : {p // p ∈ Fm.P}, p ∈ Fm.Om ↔ ¬ (Fm.FP p.1).PrimeTo) ∧
  (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ p ∈ Fm.P, LocNG.nn (Fm.R p) (Fm.d0 p) ≠ ⊤) ∧
  0 ≤ Fm.V0 ∧ (∀ c, 0 ≤ Fm.rw c) ∧ Fm.toL.MassRatioAt C0n D.R.rS ∧ Fm.toL.Unfold ∧
  (∀ x ∈ S, N.a2 x.1 γ x.2 = a2W Fm.toL (amp Fm.toL) x.1 x.2) ∧ N.Hh γ = Fm.toL.Htot ∧
  0 < Fm.toL.ngenTot ∧ Fm.toL.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN D.R.rS * N.n γ

theorem famOK_iff {Z : LocDat D} {τ : Type} {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (γ : PN.Pts D.host.E D.R.rS) (S : Finset (Cl × Nu)) (C0n : ℕ) (AAre : ℝ)
    (Fm : LocFam Z Cl Nu) : FamOK N γ S C0n AAre Fm ↔ FamOKS N γ S C0n AAre (fun L => L.ampNG) Fm := by
  unfold FamOK FamOKS
  simp only [localAmplitudeSq_eq_weighted]

theorem localLe_of_fam {Z : LocDat D} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (C1 C0n : ℕ) (AAre : ℝ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS (C1 : ℝ))
    (h : ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ Fm : LocFam Z Cl Nu, FamOK N γ S C0n AAre Fm) :
    LocalInputLe X N C1 C0n D.R.k AAre := by
  intro γ hγ S
  obtain ⟨Fm, hR, hex, hOm, hD, hn, hV0, hrw, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  have hrank : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    rw [finrank_Vp]
    have h1 := D.R.r_eq
    have h2 : 2 * D.R.rS + 2 = D.R.m := by
      have hm2 := D.R.two_le_m
      obtain ⟨j, hj⟩ := D.R.m_even
      simp only [Formalism.BasicNotions.Ranks.rS]; omega
    omega
  have hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ) := fun p hp =>
    hQ (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p) (Z.agree p).1 (Vp D p) (locH Z p) (hrank p) (Fm.FP p) (hR p hp)
  have hq2 : ∀ p ∈ Fm.P, 2 ≤ LocNG.qF (D.s.atP p).Fp := fun p hp => Formalism.MainNotions.KappaEndpoints.two_le_residue_card (Z.agree p).1
  have hqH : ∀ p ∈ Fm.P, ¬ (Fm.FP p).PrimeTo → (LocNG.qF (D.s.atP p).Fp : ℝ) ≤ (Fm.FP p).Hp := fun p hp hpr =>
    Formalism.L2.SG.Pf.residue_le_height_nonprime (Z.agree p).1 (hR p hp) (hex p hp) hpr
  have hH1 : ∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp := by
    intro p hp
    by_cases hpr : (Fm.FP p).PrimeTo
    · exact le_of_eq ((hNG p hp (Fm.R p) (Fm.d0 p)).2.2.2 hpr).1.symm
    · have h2 : (2 : ℝ) ≤ (LocNG.qF (D.s.atP p).Fp : ℝ) := by exact_mod_cast hq2 p hp
      linarith [hqH p hp hpr]
  have hHp : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp := fun p hp => le_trans zero_le_one (hH1 p hp)
  have hB : Fm.toL.Basic := by
    refine ⟨fun p d => ?_, fun p => hH1 p.1 p.2, fun p => hq2 p.1 p.2, fun p hp => hqH p.1 p.2 ((hOm p).1 hp),
      fun p => ENNReal.toReal_nonneg, hV0, hrw⟩
    show 0 ≤ LocNG.Datum.wt (Fm.d0 p.1) d.1
    unfold LocNG.Datum.wt LocNG.volRel
    positivity
  exact ⟨Fm.toL, hB, ngAt_toL Fm C1 hk hNG hD hn hHp, hM, hU, ha, hH, hpos, hle⟩

end Fam

section Step

def zOf {D : D7} {X : HidaSetting D} (Y : Full X) : LocDat D := ⟨Y.δ, Y.M, Y.agree⟩

def StepFamC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (Y.tO u u') (NOf2 Y u u' (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u') × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u')) (NuC D),
            FamOK (NOf2 Y u u' (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA) Fm

theorem stepLocPinnedC_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFamC) : StepLocPinnedC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLe_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩


end Step

end Formalism.L2.SG.NGLocModel
end
end
