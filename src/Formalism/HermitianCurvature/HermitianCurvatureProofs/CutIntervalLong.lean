import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealWeightedForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupremumAIsMajorant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RoomOffGridSymmetric
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCutInside

section
namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd

def LevelOneWordEstimate : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℝ → ℝ) (w : List (Letter ℝ S)) (N : ℕ) (dl Y : ℝ),
    8 ≤ N → w.length ≤ N → (N : ℝ) ^ 2 / 8 ≤ dl →
    (∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) →
    q Y ≠ 0 →
    Real.exp (-2) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp 2

private lemma exp_le_succ_div_self_le_exp_of_le_abs {z dl : ℝ} (hdl : 8 ≤ dl) (hz : dl ≤ |z|) :
    Real.exp (-2 * (1 / dl)) ≤ (z + 1) / z ∧ (z + 1) / z ≤ Real.exp (1 / dl) := by
  have hdl0 : 0 < dl := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, abs_zero] at hz
    linarith
  have hx : |1 / z| ≤ 1 / dl := by
    rw [abs_div, abs_one]
    exact one_div_le_one_div_of_le hdl0 hz
  have hx8 : 1 / dl ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hdl
  have hx0 : 0 < 1 / dl := by positivity
  rw [add_div, div_self hz0]
  have h1 := abs_le.mp hx
  constructor
  · have hexp : 1 + 2 * (1 / dl) ≤ Real.exp (2 * (1 / dl)) := by
      linarith [Real.add_one_le_exp (2 * (1 / dl))]
    have hone : Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hpos := Real.exp_pos (-2 * (1 / dl))
    have h2 : Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) ≤ 1 := by
      calc Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl))
          ≤ Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) := mul_le_mul_of_nonneg_left hexp hpos.le
        _ = 1 := hone
    have h3 : Real.exp (-2 * (1 / dl)) ≤ 1 - 1 / dl := by
      by_contra hc
      push_neg at hc
      have h4 : (1 - 1 / dl) * (1 + 2 * (1 / dl)) < Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) :=
        mul_lt_mul_of_pos_right hc (by positivity)
      nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / dl))]
    linarith [h1.1]
  · linarith [Real.add_one_le_exp (1 / dl), h1.2]

private lemma exp_le_qw_div_le_exp_of_far_letters {S : Type} (q : ℝ → ℝ) (dl Y : ℝ) (hdl : 8 ≤ dl) (hq : q Y ≠ 0)
    (w : List (Letter ℝ S))
    (hw : ∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) :
    Real.exp (-2 * (1 / dl) * w.length) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp (1 / dl * w.length) := by
  induction w with
  | nil => simp [qw, div_self hq]
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))
    have hl := hw l (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨F, hF, hF1, hF2⟩ : ∃ F, qw q (l :: w) Y / q Y = qw q w Y / q Y * F ∧
        Real.exp (-2 * (1 / dl)) ≤ F ∧ F ≤ Real.exp (1 / dl) := by
      cases hp : l.plus
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hl
        have hz : dl ≤ |l.pt - Y - 1| := by
          rw [show l.pt - Y - 1 = -(Y - (l.pt - 1)) by ring, abs_neg]
          exact hl.2
        refine ⟨(l.pt - Y - 1 + 1) / (l.pt - Y - 1), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hz⟩
        simp only [qw, hp, Bool.false_eq_true, ↓reduceIte]
        rw [mul_div_right_comm, show l.pt - Y - 1 + 1 = l.pt - Y by ring]
      · simp only [hp, ↓reduceIte] at hl
        refine ⟨(Y - l.pt + 1) / (Y - l.pt), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hl⟩
        simp only [qw, hp, ↓reduceIte]
        rw [mul_div_right_comm]
    have hA : 0 < Real.exp (-2 * (1 / dl) * w.length) := Real.exp_pos _
    have hr0 : 0 ≤ qw q w Y / q Y := le_trans hA.le ih1
    have hF0 : 0 ≤ F := le_trans (Real.exp_pos _).le hF1
    rw [hF, List.length_cons]
    push_cast
    constructor
    · calc Real.exp (-2 * (1 / dl) * ((w.length : ℝ) + 1))
          = Real.exp (-2 * (1 / dl) * w.length) * Real.exp (-2 * (1 / dl)) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ qw q w Y / q Y * F := mul_le_mul ih1 hF1 (Real.exp_pos _).le hr0
    · calc qw q w Y / q Y * F ≤ Real.exp (1 / dl * w.length) * Real.exp (1 / dl) :=
          mul_le_mul ih2 hF2 hF0 (Real.exp_pos _).le
        _ = Real.exp (1 / dl * ((w.length : ℝ) + 1)) := by
            rw [← Real.exp_add]
            ring_nf

theorem level_one_word_estimate : LevelOneWordEstimate := by
  intro S _ _ q w N dl Y hN hlen hdl hw hq
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hdl8 : 8 ≤ dl := by nlinarith [mul_le_mul hN8 hN8 (by norm_num) (by linarith)]
  obtain ⟨h1, h2⟩ := exp_le_qw_div_le_exp_of_far_letters q dl Y hdl8 hq w hw
  have hdl0 : 0 < dl := by linarith
  have hlenR : (w.length : ℝ) ≤ N := by exact_mod_cast hlen
  have hx : (1 / dl) * w.length ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hdl0]
    nlinarith [mul_le_mul_of_nonneg_left hN8 (by linarith : (0 : ℝ) ≤ N)]
  constructor
  · calc Real.exp (-2) ≤ Real.exp (-2 * (1 / dl) * w.length) := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ _ := h1
  · calc _ ≤ Real.exp (1 / dl * w.length) := h2
      _ ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)

end Formalism.FourierDecayAlt.P.PBD
end

section
namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

def nodeOf (x : C.Letter) : ℝ := if x.1 then x.2 else x.2 - 1

def Sep (x y : C.Letter) : Prop := ∀ δ : ℤ, -2 ≤ δ → δ ≤ 2 → 2 < |x.2 - y.2 + δ|

def pushU {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) : Finset (List C.Letter) :=
  univ.image fun j : Fin K → Fin (d + 1) => mk (List.ofFn fun b => grid b (j b))

def pushTh {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (a : List C.Letter) : ℝ :=
  ∑ j : Fin K → Fin (d + 1), if mk (List.ofFn fun b => grid b (j b)) = a then F7.thGrid grid j else 0

theorem sep_symm {x y : C.Letter} (h : Sep x y) : Sep y x := by
  intro δ h1 h2
  have h' := h (-δ) (by omega) (by omega)
  rw [show y.2 - x.2 + (δ : ℝ) = -(x.2 - y.2 + ((-δ : ℤ) : ℝ)) by push_cast; ring, abs_neg]
  exact h'

theorem sep_of_four {x y : C.Letter} (h : 4 < |x.2 - y.2|) : Sep x y := by
  intro δ h1 h2
  have hδ1 : (-2 : ℝ) ≤ δ := by exact_mod_cast h1
  have hδ2 : (δ : ℝ) ≤ 2 := by exact_mod_cast h2
  rcases lt_abs.mp h with h | h
  · exact lt_abs.mpr (Or.inl (by linarith))
  · exact lt_abs.mpr (Or.inr (by linarith))

theorem pairwise_iff_idx (L : List C.Letter) :
    L.Pairwise Sep ↔ ∀ (j j' : ℕ) (hj : j < L.length) (hj' : j' < L.length), j ≠ j' → Sep (L[j]'hj) (L[j']'hj') := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h j j' hj hj' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h j j' hj hj' hlt
    · exact sep_symm (h j' j hj' hj hlt)
  · intro h j j' hj hj' hlt
    exact h j j' hj hj' (ne_of_lt hlt)

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def AdmList (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (L : List C.Letter) : Prop :=
  (∀ j (hj : j < L.length), nodeOf (L[j]'hj) ∈ S.grid v (L.length - j) ∪ S.grid1 v) ∧ L.Pairwise Sep

theorem admissible_list_of_word (S : C.HidaSetting E Wp Wq) (w : S.W) (v : Fin S.f) : AdmList S v (w.1 v) := by
  obtain ⟨⟨h1, h2⟩, -⟩ := w.2
  exact ⟨fun j hj => h1 v j hj, (pairwise_iff_idx _).2 fun j j' hj hj' hne δ hδ1 hδ2 => h2 v j j' hj hj' hne δ hδ1 hδ2⟩

theorem ntop_ge (S : C.HidaSetting E Wp Wq) : (20 : ℝ) ≤ S.Ntop := by
  have h : 20 ≤ S.Ntop := by
    unfold C.HidaSetting.Ntop C.Kst
    omega
  exact_mod_cast h

theorem admissible_at_of_admissible_list (S : C.HidaSetting E Wp Wq) (w : S.W) (v : Fin S.f) (L : List C.Letter)
    (hL : AdmList S v L) (hlen : L.length ≤ S.Ntop) : D.AdmAt S v L := by
  classical
  obtain ⟨hL1, hL2⟩ := hL
  obtain ⟨⟨h1, h2⟩, hc⟩ := w.2
  refine ⟨⟨Function.update w.1 v L, ⟨⟨fun u => ?_, fun u => ?_⟩, ?_⟩⟩, by simp⟩
  · by_cases hu : u = v
    · subst hu
      generalize hM : Function.update w.1 u L u = M
      have hML : M = L := by rw [← hM]; simp
      subst hML
      exact hL1
    · generalize hM : Function.update w.1 v L u = M
      have hML : M = w.1 u := by rw [← hM]; simp [hu]
      subst hML
      exact h1 u
  · by_cases hu : u = v
    · subst hu
      generalize hM : Function.update w.1 u L u = M
      have hML : M = L := by rw [← hM]; simp
      subst hML
      exact fun j j' hj hj' hne δ hδ1 hδ2 => (pairwise_iff_idx M).1 hL2 j j' hj hj' hne δ hδ1 hδ2
    · generalize hM : Function.update w.1 v L u = M
      have hML : M = w.1 u := by rw [← hM]; simp [hu]
      subst hML
      exact h2 u
  · unfold C.Word.cnt
    refine Finset.sup_le fun u _ => ?_
    by_cases hu : u = v
    · subst hu
      simpa using hlen
    · have hM : Function.update w.1 v L u = w.1 u := by simp [hu]
      rw [hM]
      exact (Finset.le_sup (f := fun u => (w.1 u).length) (Finset.mem_univ u)).trans hc

theorem admissible_list_prepend (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (pre a : List C.Letter) (ha : AdmList S v a)
    (hpre : ∀ j (hj : j < pre.length), nodeOf (pre[j]'hj) ∈ S.grid v (pre.length + a.length - j) ∪ S.grid1 v)
    (hpp : pre.Pairwise Sep) (hpa : ∀ x ∈ pre, ∀ y ∈ a, Sep x y) : AdmList S v (pre ++ a) := by
  refine ⟨fun j hj => ?_, List.pairwise_append.2 ⟨hpp, ha.2, hpa⟩⟩
  by_cases hjp : j < pre.length
  · rw [List.getElem_append_left hjp, List.length_append]
    exact hpre j hjp
  · have hj2 : j - pre.length < a.length := by
      rw [List.length_append] at hj
      omega
    rw [List.getElem_append_right (by omega), List.length_append,
      show pre.length + a.length - j = a.length - (j - pre.length) by omega]
    exact ha.1 (j - pre.length) hj2

theorem sep_grid (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) {b b' : ℕ} {y y' : ℝ}
    (hy : y ∈ S.grid v b) (hy' : y' ∈ S.grid v b') (hne : b ≠ b') {e e' : ℝ}
    (he : e ∈ ({0, 1} : Finset ℝ)) (he' : e' ∈ ({0, 1} : Finset ℝ)) :
    (S.Ntop : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')| := by
  obtain ⟨hlen, hgr, -⟩ := hG v
  have hN : (20 : ℝ) ≤ S.Ntop := ntop_ge S
  obtain ⟨-, -, hyl, hyu⟩ := hgr b y hy
  obtain ⟨-, -, hyl', hyu'⟩ := hgr b' y' hy'
  simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
  have he0 : 0 ≤ e ∧ e ≤ 1 := by rcases he with rfl | rfl <;> norm_num
  have he0' : 0 ≤ e' ∧ e' ≤ 1 := by rcases he' with rfl | rfl <;> norm_num
  unfold C.gridL at hyl hyu hyl' hyu'
  have hNpos : (0 : ℝ) < 6 * S.Ntop := by positivity
  have hΔ : (S.Ntop : ℝ) ^ 2 + 1 ≤ (S.cutHi v - S.cutLo v) / (6 * S.Ntop) := by
    rw [le_div_iff₀ hNpos]
    nlinarith
  set Δ := (S.cutHi v - S.cutLo v) / (6 * S.Ntop) with hΔdef
  have hΔ0 : 0 ≤ Δ := by nlinarith
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hbb : (b : ℝ) + 1 ≤ b' := by exact_mod_cast hlt
    have key : 2 * (b : ℝ) * Δ + 2 * Δ ≤ 2 * (b' : ℝ) * Δ := by nlinarith
    exact le_abs.2 (Or.inr (by linarith))
  · have hbb : (b' : ℝ) + 1 ≤ b := by exact_mod_cast hlt
    have key : 2 * (b' : ℝ) * Δ + 2 * Δ ≤ 2 * (b : ℝ) * Δ := by nlinarith
    exact le_abs.2 (Or.inl (by linarith))

theorem pt_split (x : C.Letter) : x.2 = nodeOf x + (if x.1 then 0 else 1) ∧
    (if x.1 then (0 : ℝ) else 1) ∈ ({0, 1} : Finset ℝ) := by
  rcases x with ⟨_ | _, p⟩ <;> simp [nodeOf]

theorem nodeOf_mem_grid_or_grid1 (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (ha : AdmList S v a) (z : C.Letter)
    (hz : z ∈ a) : (∃ n, n ≤ a.length ∧ nodeOf z ∈ S.grid v n) ∨ nodeOf z ∈ S.grid1 v := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  rcases Finset.mem_union.1 (ha.1 j hj) with h | h
  · exact Or.inl ⟨a.length - j, Nat.sub_le _ _, h⟩
  · exact Or.inr h

theorem four_lt_sq (S : C.HidaSetting E Wp Wq) : (4 : ℝ) < (S.Ntop : ℝ) ^ 2 / 8 ∧ (4 : ℝ) < (S.Ntop : ℝ) ^ 2 + 1 := by
  have h := ntop_ge S
  constructor <;> nlinarith

theorem grid_point_far_from_letters (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : AdmList S v a) {B : ℕ} {y : ℝ} (hy : y ∈ S.grid v B) (hB : a.length < B) (z : C.Letter) (hz : z ∈ a)
    {e : ℝ} (he : e ∈ ({0, 1} : Finset ℝ)) : 4 < |(y + e) - z.2| := by
  have hz' := (pt_split z).1
  have he' := (pt_split z).2
  rcases nodeOf_mem_grid_or_grid1 S v a ha z hz with ⟨n, hn, hnode⟩ | hnode
  · have h := sep_grid S hG v hy hnode (by omega) he he'
    rw [hz']
    linarith [(four_lt_sq S).2]
  · have h := (hG v).2.2.2.2.1 (nodeOf z) hnode B y hy _ he' e he
    rw [hz', abs_sub_comm]
    linarith [(four_lt_sq S).2]

theorem grid1_point_far_from_letters (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : AdmList S v a) {y : ℝ} (hy : y ∈ S.grid1 v) (hyn : y ∉ a.map nodeOf) (z : C.Letter) (hz : z ∈ a)
    {e : ℝ} (he : e ∈ ({0, 1} : Finset ℝ)) : 4 < |(y + e) - z.2| := by
  have hz' := (pt_split z).1
  have he' := (pt_split z).2
  rcases nodeOf_mem_grid_or_grid1 S v a ha z hz with ⟨n, hn, hnode⟩ | hnode
  · have h := (hG v).2.2.2.2.1 y hy n (nodeOf z) hnode e he _ he'
    rw [hz']
    linarith [(four_lt_sq S).2]
  · have hne : y ≠ nodeOf z := fun h => hyn (by rw [h]; exact List.mem_map.2 ⟨z, hz, rfl⟩)
    have h := (hG v).2.2.2.1 y hy (nodeOf z) hnode hne e he _ he'
    rw [hz']
    linarith [(four_lt_sq S).1]

theorem extend (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (hC : KB.CutInside S) (v : Fin S.f) (a : List C.Letter)
    (haA : D.AdmAt S v a) (ys : List ℝ) (H1 : ys.Pairwise fun y y' => 4 < |y - y'|)
    (H2 : ∀ y ∈ ys, ∀ z ∈ a, 4 < |(y + 0) - z.2| ∧ 4 < |(y + 1) - z.2|)
    (H3 : ∀ i (hi : i < ys.length), ys[i] ∈ S.grid v (ys.length + a.length - i) ∪ S.grid1 v)
    (hlen : ys.length + a.length ≤ S.Ntop) :
    D.AdmAt S v (KB.plusW ys a) ∧ D.AdmAt S v (KB.minusW ys a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW ys a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW ys a) := by
  obtain ⟨w, hw⟩ := haA
  have ha : AdmList S v a := by rw [← hw]; exact admissible_list_of_word S w v
  have hcut : ∀ y, ((∃ n, y ∈ S.grid v n) ∨ y ∈ S.grid1 v) → ∀ e ∈ ({0, 1} : Finset ℝ),
      I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) (y + e) := by
    intro y hy e he
    obtain ⟨h1, h2, -⟩ := (hG v).2.2.2.2.2 y hy
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    apply hC v
    rw [Set.mem_Icc]
    unfold C.HidaSetting.cutLo C.HidaSetting.cutHi
    rcases he with rfl | rfl <;> constructor <;> linarith
  have hLcut : ∀ L, AdmList S v L → KB.CutWord (D.parOf S v) (S.l + 1) L := by
    intro L hL
    refine (cutWord_iff _ _ L).2 ⟨fun x hx => ?_, hL.2.imp fun h => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      rw [(pt_split _).1]
      refine hcut _ ?_ _ (pt_split _).2
      rcases Finset.mem_union.1 (hL.1 j hj) with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    · have h0 := h 0 (by norm_num) (by norm_num)
      simpa using h0
  have hP : AdmList S v (KB.plusW ys a) := by
    rw [plusW_eq]
    refine admissible_list_prepend S v _ a ha ?_ ?_ ?_
    · intro j hj
      have hj' : j < ys.length := by simpa using hj
      simpa [nodeOf] using H3 j hj'
    · rw [List.pairwise_map]
      exact H1.imp fun h => sep_of_four h
    · intro x hx z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact sep_of_four (by simpa using (H2 y hy z hz).1)
  have hM : AdmList S v (KB.minusW ys a) := by
    rw [minusW_eq]
    refine admissible_list_prepend S v _ a ha ?_ ?_ ?_
    · intro j hj
      have hj' : j < ys.length := by simpa using hj
      simpa [nodeOf] using H3 j hj'
    · rw [List.pairwise_map]
      exact H1.imp fun h => sep_of_four (by simpa using h)
    · intro x hx z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact sep_of_four (by simpa using (H2 y hy z hz).2)
  have hlenP : (KB.plusW ys a).length ≤ S.Ntop := by rw [plusW_eq]; simpa using hlen
  have hlenM : (KB.minusW ys a).length ≤ S.Ntop := by rw [minusW_eq]; simpa using hlen
  exact ⟨admissible_at_of_admissible_list S w v _ hP hlenP, admissible_at_of_admissible_list S w v _ hM hlenM, hLcut _ hP, hLcut _ hM⟩

end

section new

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    F7.lagCo y j ≠ 0 := by
  unfold F7.lagCo
  exact Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero (sub_ne_zero.2 fun h => Finset.ne_of_mem_erase hi (hy h).symm)

theorem thGrid_nonneg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) :
    0 ≤ F7.thGrid grid j := by
  unfold F7.thGrid
  exact Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)

theorem thGrid_sum {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    ∑ j, F7.thGrid grid j = 1 := by
  unfold F7.thGrid
  have h := Finset.prod_univ_sum (fun _ : Fin K => (Finset.univ : Finset (Fin (d + 1))))
    (fun a i => |F7.lagCo (grid a) i| / ∑ i, |F7.lagCo (grid a) i|)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← Finset.sum_div, div_self]
  have h0 : 0 < |F7.lagCo (grid b) 0| := abs_pos.2 (lagCo_ne_zero _ (hinj b) 0)
  exact (Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨0, Finset.mem_univ _, h0⟩).ne'

theorem locProb_push (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (n' : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b)) (mk : List ℝ → List C.Letter)
    (hmk : ∀ j : Fin K → Fin (d + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (j b))) ∧
      (mk (List.ofFn fun b => grid b (j b))).length ≤ n') :
    KB.LocProb S v n' (pushU grid mk) (pushTh grid mk) := by
  classical
  refine ⟨⟨fun a => ?_, fun a ha => ?_, ?_⟩, fun a ha => ?_⟩
  · unfold pushTh
    exact Finset.sum_nonneg fun j _ => by
      split_ifs
      exacts [thGrid_nonneg grid j, le_refl 0]
  · unfold pushTh
    refine Finset.sum_eq_zero fun j _ => if_neg fun h => ha ?_
    rw [← h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  · unfold pushTh
    rw [Finset.sum_comm, ← thGrid_sum grid hinj]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq, if_pos (by unfold pushU; exact Finset.mem_image_of_mem _ (Finset.mem_univ j))]
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    exact hmk j

end new

end

def NewLetters : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → KB.GridsRich S → KB.CutInside S →
    ∀ (v : Fin S.f) (a : List C.Letter) (K n : ℕ), D.AdmAt S v a → a.length + K ≤ S.Ntop → n ≤ 2 * S.G.r →
    KB.CutWord (D.parOf S v) (S.l + 1) a ∧
    ∃ grid : Fin K → Fin (n + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ j, |F7.lagCo (grid b) j| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ n) ∧
      (∀ (b : Fin K) j, grid b j ∈ S.grid v (a.length + K - (b : ℕ))) ∧
      (∀ j : Fin K → Fin (n + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
        (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'|) ∧
      KB.LocProb S v (a.length + K) (pushU grid fun ys => KB.plusW ys a) (pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (pushU grid fun ys => KB.minusW ys a) (pushTh grid fun ys => KB.minusW ys a)

def NewLetters1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → KB.GridsRich S → KB.CutInside S →
    ∀ (v : Fin S.f) (a : List C.Letter) (K : ℕ), D.AdmAt S v a → a.length + K ≤ S.Ntop →
    ∃ ys : List ℝ, ys.length = K ∧ ys.Nodup ∧ (∀ y ∈ ys, y ∈ S.grid1 v) ∧
      D.AdmAt S v (KB.plusW ys a) ∧ D.AdmAt S v (KB.minusW ys a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW ys a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW ys a) ∧
      ys.Pairwise fun y y' => 4 < |y - y'|

theorem newLetters : NewLetters := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S hG hR hC v a K n haA hlen hn
  obtain ⟨w, hw⟩ := haA
  have ha : AdmList S v a := hw ▸ admissible_list_of_word S w v
  refine ⟨hw ▸ cutWord_of_adm S hG hC w v, ?_⟩
  have hex : ∀ b : Fin K, ∃ y : Fin (n + 1) → ℝ, Function.Injective y ∧
      (∀ j, y j ∈ S.grid v (a.length + K - (b : ℕ))) ∧
      ∑ j, |F7.lagCo y j| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ n :=
    fun b => (hR v).2 _ (by omega) (by omega) n hn
  choose grid hinj hmem hbd using hex
  have h4 := four_lt_sq S
  have key : ∀ j : Fin K → Fin (n + 1),
      D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
      D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
      (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'| := by
    intro j
    have H1 : (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'| := by
      rw [List.pairwise_ofFn]
      intro i i' hii'
      have hlt : (i : ℕ) < i' := hii'
      have hi := i.isLt
      have hi' := i'.isLt
      have := sep_grid S hG v (hmem i (j i)) (hmem i' (j i')) (by omega) (e := 0) (e' := 0) (by simp) (by simp)
      simp only [add_zero] at this
      linarith [h4.2]
    have H2 : ∀ y ∈ List.ofFn (fun b => grid b (j b)), ∀ z ∈ a, 4 < |(y + 0) - z.2| ∧ 4 < |(y + 1) - z.2| := by
      intro y hy z hz
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hiK : i < K := by simpa using hi
      rw [List.getElem_ofFn]
      have hB : a.length < a.length + K - ((⟨i, hiK⟩ : Fin K) : ℕ) := by show a.length < a.length + K - i; omega
      exact ⟨grid_point_far_from_letters S hG v a ha (hmem ⟨i, hiK⟩ (j ⟨i, hiK⟩)) hB z hz (by simp),
        grid_point_far_from_letters S hG v a ha (hmem ⟨i, hiK⟩ (j ⟨i, hiK⟩)) hB z hz (by simp)⟩
    have H3 : ∀ i (hi : i < (List.ofFn fun b => grid b (j b)).length),
        (List.ofFn fun b => grid b (j b))[i] ∈
          S.grid v ((List.ofFn fun b => grid b (j b)).length + a.length - i) ∪ S.grid1 v := by
      intro i hi
      rw [List.getElem_ofFn]
      refine Finset.mem_union_left _ ?_
      have := hmem ⟨i, by simpa using hi⟩ (j ⟨i, by simpa using hi⟩)
      simpa [Nat.add_comm] using this
    obtain ⟨e1, e2, e3, e4⟩ := extend S hG hC v a ⟨w, hw⟩ _ H1 H2 H3 (by simp; omega)
    exact ⟨e1, e2, e3, e4, H1⟩
  refine ⟨grid, hinj, hbd, hmem, key, ?_, ?_⟩
  · exact locProb_push S v _ grid hinj _ fun j => ⟨(key j).1, by rw [plusW_eq]; simp; omega⟩
  · exact locProb_push S v _ grid hinj _ fun j => ⟨(key j).2.1, by rw [minusW_eq]; simp; omega⟩

theorem newLetters1 : NewLetters1 := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S hG hR hC v a K haA hlen
  classical
  obtain ⟨w, hw⟩ := haA
  have ha : AdmList S v a := by rw [← hw]; exact admissible_list_of_word S w v
  have hT1 : K ≤ (S.grid1 v \ (a.map nodeOf).toFinset).card := by
    have h1 := Finset.le_card_sdiff ((a.map nodeOf).toFinset) (S.grid1 v)
    have h2 := List.toFinset_card_le (a.map nodeOf)
    have h3 := (hR v).1
    rw [List.length_map] at h2
    omega
  obtain ⟨U, hUT, hUc⟩ := Finset.exists_subset_card_eq hT1
  have hmem : ∀ y ∈ U.toList, y ∈ S.grid1 v ∧ y ∉ a.map nodeOf := by
    intro y hy
    have h := hUT (Finset.mem_toList.1 hy)
    rw [Finset.mem_sdiff, List.mem_toFinset] at h
    exact h
  have hpw : U.toList.Pairwise fun y y' => 4 < |y - y'| := by
    refine U.nodup_toList.pairwise_of_forall_ne fun y hy y' hy' hne => ?_
    have h := (hG v).2.2.2.1 y (hmem y hy).1 y' (hmem y' hy').1 hne 0 (by simp) 0 (by simp)
    simp only [add_zero] at h
    linarith [(four_lt_sq S).1]
  have hlen2 : U.toList.length + a.length ≤ S.Ntop := by
    rw [Finset.length_toList, hUc]
    omega
  obtain ⟨h1, h2, h3, h4⟩ := extend S hG hC v a ⟨w, hw⟩ U.toList hpw
    (fun y hy z hz => ⟨grid1_point_far_from_letters S hG v a ha (hmem y hy).1 (hmem y hy).2 z hz (by simp),
      grid1_point_far_from_letters S hG v a ha (hmem y hy).1 (hmem y hy).2 z hz (by simp)⟩)
    (fun i hi => Finset.mem_union_right _ (hmem _ (List.getElem_mem hi)).1) hlen2
  exact ⟨U.toList, by rw [Finset.length_toList, hUc], U.nodup_toList, fun y hy => (hmem y hy).1, h1, h2, h3, h4,
    hpw⟩

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.new_letters_admissible : Formalism.FourierDecayAlt.P.PBD.NewLetters := Formalism.FourierDecayAlt.P.PBD.newLetters
theorem Formalism.FourierDecayAlt.P.new_letters_admissible_level_one : Formalism.FourierDecayAlt.P.PBD.NewLetters1 := Formalism.FourierDecayAlt.P.PBD.newLetters1
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

section node

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem ntop_eq_N' (S : C.HidaSetting E Wp Wq) : (S.Ntop : ℝ) = S.G.N := by
  unfold C.HidaSetting.Ntop Sz.Glob.N C.Kst
  push_cast
  ring

theorem cutI_eq (S : C.HidaSetting E Wp Wq) (v : Fin S.f) :
    (S.G.place (S.pl v)).cutI S.l = Set.Icc (S.cutLo v) (S.cutHi v) := by
  ext Y
  simp only [Sz.Cfg.cutI, Set.mem_ofPred_eq, Set.mem_Icc, C.HidaSetting.cutLo, C.HidaSetting.cutHi]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem qC_re (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (y : ℝ) :
    (M.qC (D.parOf S v) (y : ℂ)).re = (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y := by
  rw [PBF.qC_ofReal, Complex.ofReal_re]
  rfl

variable {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem q_pos_cut (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (y : ℝ)
    (hy : y ∈ Set.Icc (S.cutLo v) (S.cutHi v)) : 0 < (M.qC (D.parOf S v) (y : ℂ)).re := by
  have hy' := PBCut.cutInside_of_built hB v y hy
  obtain ⟨-, -, -, -, -, -, -, hl1, hlk, -⟩ := hB
  rw [PBF.qC_ofReal, Complex.ofReal_re]
  exact PBF.qreal_pos (D.parOf S v) (p v).hP.1 (S.l + 1) (by omega) (by show S.l + 1 ≤ S.G.k; omega) y hy'

theorem core_bdd (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) :
    BddAbove ((fun Y => (S.G.place (S.pl v)).core S.de S.de' S.T S.T' Y) '' Set.Icc (S.cutLo v) (S.cutHi v)) := by
  apply IsCompact.bddAbove_image isCompact_Icc
  intro Y hY
  have hq : 0 < (S.G.place (S.pl v)).q S.de S.de' S.T S.T' Y := by
    rw [← qC_re]
    exact q_pos_cut hB v Y hY
  have hPc : Continuous fun Y => (S.G.place (S.pl v)).P Y := by
    unfold Sz.Cfg.P
    fun_prop
  have hqc : Continuous fun Y => (S.G.place (S.pl v)).q S.de S.de' S.T S.T' Y := by
    unfold Sz.Cfg.q
    fun_prop
  have hnum : Continuous fun Y => (S.G.place (S.pl v)).P Y * (S.G.place (S.pl v)).P (Y + 1) :=
    hPc.mul (hPc.comp (continuous_id.add continuous_const))
  have hf : ContinuousAt (fun Y => (S.G.place (S.pl v)).P Y * (S.G.place (S.pl v)).P (Y + 1) /
      (S.G.place (S.pl v)).q S.de S.de' S.T S.T' Y) Y :=
    hnum.continuousAt.div hqc.continuousAt hq.ne'
  exact (Real.continuous_sqrt.continuousAt.comp (continuous_abs.continuousAt.comp hf)).continuousWithinAt

theorem supA_nonneg (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (hk : 0 < S.G.ka) (v : Fin S.f) (one : Bool) :
    0 ≤ J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := by
  have key : ∀ T0 : Set ℝ, 0 ≤ sSup ((fun Y => S.G.g ^ S.G.m *
      (S.G.place (S.pl v)).be S.G.ka S.de S.de' S.T S.T' Y) '' T0) := by
    intro T0
    apply Real.sSup_nonneg
    rintro _ ⟨Y, -, rfl⟩
    apply mul_nonneg (pow_nonneg hg.le _)
    unfold Sz.Cfg.be
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hk.le _)) (Real.sqrt_nonneg _)
  unfold J.supA
  apply div_nonneg
  · cases one
    · simp only [Bool.false_eq_true, ↓reduceIte, Sz.Glob.supI]
      exact key _
    · simp only [↓reduceIte, Sz.Glob.cutSupLong]
      exact key _
  · exact mul_nonneg (pow_nonneg hg.le _) (inv_nonneg.mpr (pow_nonneg hk.le _))

theorem core_le_supA (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (one : Bool) (y : ℝ)
    (hy : if one then y ∈ (S.G.place (S.pl v)).cutIntervalLong S.l S.G.N else y ∈ (S.G.place (S.pl v)).cutI S.l) :
    (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y ≤ J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := by
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hG, -⟩ := id hB
  have hg : 0 < S.G.g := by
    unfold Sz.Glob.g
    exact mul_pos (Nat.cast_pos.mpr hg1) (Nat.cast_pos.mpr hg2)
  have hv : 0 < S.G.v := by
    rw [S.hv]
    have := Jx5.rd_pos' (E := E)
    linarith
  have hk : 0 < S.G.ka := by
    unfold Sz.Glob.ka
    exact div_pos Real.pi_pos hv
  have hsub := Jx5.sup_core S.G S.de S.de' S.T S.T' (S.pl v) hg hk
  have hbdd : BddAbove ((fun Y => (S.G.place (S.pl v)).core S.de S.de' S.T S.T' Y) ''
      (S.G.place (S.pl v)).cutI S.l) := by
    rw [cutI_eq]
    exact core_bdd hB v
  unfold J.supA
  cases one
  · simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
    unfold Sz.Glob.supI
    rw [hsub]
    exact le_csSup hbdd ⟨y, hy, rfl⟩
  · simp only [↓reduceIte] at hy ⊢
    unfold Sz.Glob.cutSupLong
    rw [hsub]
    refine le_csSup (hbdd.mono (Set.image_mono ?_)) ⟨y, hy, rfl⟩
    intro Y hY
    simp only [Sz.Cfg.cutIntervalLong, Sz.Cfg.cutI, Set.mem_ofPred_eq] at hY ⊢
    refine ⟨hY.1, le_trans hY.2 ?_⟩
    have h1 := (hG v).1
    simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo] at h1
    rw [← ntop_eq_N' S]
    have h0 : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _
    have h3 := pow_nonneg h0 3
    linarith

end node

section nodeb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem node_far (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (y : ℝ) (one : Bool) (hy : (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
      (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)) (z : C.Letter) (hz : z ∈ a) :
    (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - PBD.nodeOf z| ∧
    (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - (PBD.nodeOf z + 1)| := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := id hB
  obtain ⟨w, hw⟩ := ha
  have hA : PBD.AdmList S v a := hw ▸ PBD.admissible_list_of_word S w v
  have hz' := PBD.nodeOf_mem_grid_or_grid1 S v a hA z hz
  suffices key : ∀ e ∈ ({0, 1} : Finset ℝ),
      (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - (PBD.nodeOf z + e)| by
    refine ⟨?_, key 1 (by simp)⟩
    simpa using key 0 (by simp)
  intro e he
  rcases hy with ⟨rfl, a', ha', -, hya'⟩ | ⟨rfl, hy1, hsep⟩
  · rw [if_neg (by decide)]
    rcases hz' with ⟨n, hn, hzn⟩ | hz1
    · have h := PBD.sep_grid S hG v hya' hzn (by omega) (e := 0) (by simp) he
      simpa using h
    · have h := (hG v).2.2.2.2.1 (PBD.nodeOf z) hz1 a' y hya' e he 0 (by simp)
      rw [abs_sub_comm] at h
      simpa using h
  · rw [if_pos rfl]
    rcases hz' with ⟨n, -, hzn⟩ | hz1
    · have h := (hG v).2.2.2.2.1 y hy1 n (PBD.nodeOf z) hzn 0 (by simp) e he
      have h8 : (S.Ntop : ℝ) ^ 2 / 8 ≤ (S.Ntop : ℝ) ^ 2 + 1 := by
        linarith [sq_nonneg (S.Ntop : ℝ)]
      simp only [add_zero] at h
      linarith
    · have hne : y ≠ PBD.nodeOf z := by
        intro hyz
        have hs : ∀ δ : ℤ, -2 ≤ δ → δ ≤ 2 → 2 < |y - z.2 + δ| := hsep z hz
        obtain ⟨b, t⟩ := z
        cases b
        · have h := hs 1 (by norm_num) (by norm_num)
          simp only [PBD.nodeOf, Bool.false_eq_true, ↓reduceIte] at hyz
          rw [hyz] at h
          norm_num at h
        · have h := hs 0 (by norm_num) (by norm_num)
          simp only [PBD.nodeOf, ↓reduceIte] at hyz
          rw [hyz] at h
          norm_num at h
      have h := (hG v).2.2.2.1 y hy1 (PBD.nodeOf z) hz1 hne 0 (by simp) e he
      simpa using h

theorem node_bound (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (haN : a.length ≤ S.Ntop) (y : ℝ) (one : Bool)
    (hy : (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
      (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)) :
    0 < (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re ∧
      |S.P v y * S.P v (y + 1)| / (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re ≤
        (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v)) ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := id hB
  have hcut : y ∈ (S.G.place (S.pl v)).cutI S.l := by
    refine ((hG v).2.2.2.2.2 y ?_).1
    rcases hy with ⟨-, a', -, -, h⟩ | ⟨-, h, -⟩
    · exact Or.inl ⟨a', h⟩
    · exact Or.inr h
  have hyc : y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    rw [← cutI_eq]
    exact hcut
  have hqpos := q_pos_cut hB v y hyc
  have hreal : ∀ l ∈ D.positionted a, l.pt.im = 0 := by
    intro l hl
    simp only [D.positionted, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    simp
  have hqim : (M.qC (D.parOf S v) (y : ℂ)).im = 0 := by
    rw [PBF.qC_ofReal, Complex.ofReal_im]
  have hconv := RealWeightedForms.qwOfReal (Fin a.length) (M.qC (D.parOf S v)) (D.positionted a) y hqim hreal
  have h8 : 8 ≤ S.Ntop := by
    unfold C.HidaSetting.Ntop C.Kst
    omega
  have hlen : ((D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length))).length
      ≤ S.Ntop := by
    simpa [D.positionted] using haN
  have hdl : (S.Ntop : ℝ) ^ 2 / 8 ≤ (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) := by
    split_ifs <;> linarith [sq_nonneg (S.Ntop : ℝ)]
  have hlet : ∀ l ∈ (D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length)),
      if l.plus then (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - l.pt| else
        (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - l.pt| ∧
          (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - (l.pt - 1)| := by
    intro l hl
    simp only [List.mem_map, D.positionted, List.mem_ofFn] at hl
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hl
    have hz : a.get i ∈ a := List.get_mem a i
    have hf := node_far hB v a ha y one hy (a.get i) hz
    simp only [Complex.ofReal_re]
    generalize a.get i = z at hf
    obtain ⟨b, t⟩ := z
    cases b
    · simp only [PBD.nodeOf, Bool.false_eq_true, ↓reduceIte, sub_add_cancel] at hf ⊢
      exact ⟨hf.2, hf.1⟩
    · simp only [PBD.nodeOf, ↓reduceIte] at hf ⊢
      exact hf.1
  have hq8 := PBD.level_one_word_estimate (Fin a.length) (fun t : ℝ => (M.qC (D.parOf S v) (t : ℂ)).re)
    ((D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length))) S.Ntop
    (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) y h8 hlen hdl hlet hqpos.ne'
  obtain ⟨hlo, -⟩ := hq8
  rw [hconv, Complex.ofReal_re]
  generalize Wd.qw (fun t : ℝ => (M.qC (D.parOf S v) (t : ℂ)).re)
    ((D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length))) y = Q at hlo ⊢
  have hlo' : Real.exp (-2) * (M.qC (D.parOf S v) (y : ℂ)).re ≤ Q := by
    have := (le_div_iff₀ hqpos).mp hlo
    linarith
  have hpos : 0 < Real.exp (-2) * (M.qC (D.parOf S v) (y : ℂ)).re := mul_pos (Real.exp_pos _) hqpos
  refine ⟨lt_of_lt_of_le hpos hlo', ?_⟩
  have hmem1 : if one then y ∈ (S.G.place (S.pl v)).cutIntervalLong S.l S.G.N else y ∈ (S.G.place (S.pl v)).cutI S.l := by
    rcases hy with ⟨rfl, -⟩ | ⟨rfl, h1, -⟩
    · rw [if_neg (by decide)]
      exact hcut
    · rw [if_pos rfl, ← ntop_eq_N' S]
      exact ((hG v).2.2.1 y h1).1
  have hcore := core_le_supA hB v one y hmem1
  have hc0 : 0 ≤ (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y := Real.sqrt_nonneg _
  have hqR := qC_re S v y
  have hcsq : ((S.G.place (S.pl v)).core S.de S.de' S.T S.T' y) ^ 2 =
      |S.P v y * S.P v (y + 1)| / (M.qC (D.parOf S v) (y : ℂ)).re := by
    unfold Sz.Cfg.core
    rw [Real.sq_sqrt (abs_nonneg _), abs_div, hqR, abs_of_pos (a := (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y) (by rw [← hqR]; exact hqpos)]
    rfl
  have hne : (M.qC (D.parOf S v) (y : ℂ)).re ≠ 0 := hqpos.ne'
  calc |S.P v y * S.P v (y + 1)| / Q
      ≤ |S.P v y * S.P v (y + 1)| / (Real.exp (-2) * (M.qC (D.parOf S v) (y : ℂ)).re) :=
        div_le_div_of_nonneg_left (abs_nonneg _) hpos hlo'
    _ = Real.exp 2 * (|S.P v y * S.P v (y + 1)| / (M.qC (D.parOf S v) (y : ℂ)).re) := by
        rw [Real.exp_neg]
        field_simp
    _ = Real.exp 2 * ((S.G.place (S.pl v)).core S.de S.de' S.T S.T' y) ^ 2 := by rw [hcsq]
    _ ≤ Real.exp 2 * (J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hcore 2) (Real.exp_pos 2).le
    _ = (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num

end nodeb

end

end Formalism.FourierDecayAlt.P.PBL
end
