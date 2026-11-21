import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Lemmata.SmulListSum.SmulListSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Core

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]

theorem vc_le_genSub (T : Fin n → Fin n → Module.End ℂ U) (S : Submodule ℂ U) : S ≤ genSub T S := by
  unfold genSub
  exact le_sInf fun X hX => hX.1

theorem vc_genSub_stable (T : Fin n → Fin n → Module.End ℂ U) (S : Submodule ℂ U) (a b : Fin n) {v : U}
    (hv : v ∈ genSub T S) : T a b v ∈ genSub T S := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro X hX
  exact hX.2 a b v (hv X hX)

theorem vc_genSub_le (T : Fin n → Fin n → Module.End ℂ U) (S X : Submodule ℂ U) (hSX : S ≤ X)
    (hX : ∀ a b, ∀ v ∈ X, T a b v ∈ X) : genSub T S ≤ X := by
  unfold genSub
  exact sInf_le ⟨hSX, hX⟩

def vcGood (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop) : Set U :=
  {w | ∃ ν, P ν ∧ ∀ a, T a a w = ((ν a : ℝ) : ℂ) • w}

theorem vcGood_smul (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop) {w : U}
    (hw : w ∈ vcGood T P) (c : ℂ) : c • w ∈ vcGood T P := by
  simp only [vcGood, Set.mem_setOf_eq] at hw ⊢
  obtain ⟨ν, hP, hν⟩ := hw
  refine ⟨ν, hP, fun a => ?_⟩
  rw [map_smul, hν a, smul_comm]

theorem vc_exists_list {G : Set U} (hs : ∀ w ∈ G, ∀ c : ℂ, c • w ∈ G) {y : U}
    (hy : y ∈ Submodule.span ℂ G) : ∃ l : List U, (∀ w ∈ l, w ∈ G) ∧ y = l.sum := by
  first | exact Bl.SmulListSum.goal1 .. | (apply Bl.SmulListSum.goal1 <;> assumption) | (intros; apply Bl.SmulListSum.goal1 <;> assumption)

theorem vc_eq_zero_of_list (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop)
    {μ : Fin n → ℝ} (hμ : ¬ P μ) :
    ∀ (N : ℕ) (l : List U), l.length = N → (∀ w ∈ l, w ∈ vcGood T P) → ∀ x : U,
      (∀ a, T a a x = ((μ a : ℝ) : ℂ) • x) → x = l.sum → x = 0 := by
  intro N
  induction N with
  | zero =>
    intro l hl _ x _ hxl
    cases l with
    | nil => simpa using hxl
    | cons w l' => simp at hl
  | succ N ih =>
    intro l hl hg x hx hxl
    cases l with
    | nil => simp at hl
    | cons w l' =>
      have hl' : l'.length = N := by simpa using hl
      have hw0 := hg w (by simp)
      simp only [vcGood, Set.mem_setOf_eq] at hw0
      obtain ⟨ν, hPν, hν⟩ := hw0
      have hne : ν ≠ μ := fun h => hμ (h ▸ hPν)
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      have hc0 : ((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast ha.symm)
      obtain ⟨D, hD⟩ : ∃ D : Module.End ℂ U, ∀ u, D u = T a a u - ((ν a : ℝ) : ℂ) • u :=
        ⟨T a a - ((ν a : ℝ) : ℂ) • 1, fun u => by simp⟩
      have h1 : D x = (((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x := by
        rw [hD, hx a, sub_smul]
      have h2 : D w = 0 := by rw [hD, hν a, sub_self]
      have h3 : D x = (l'.map D).sum := by
        rw [hxl, List.sum_cons, map_add, h2, zero_add, map_list_sum]
      have hgood : ∀ u ∈ l'.map D, u ∈ vcGood T P := by
        intro u hu
        obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
        have hg0 := hg u0 (by simp [hu0])
        simp only [vcGood, Set.mem_setOf_eq] at hg0 ⊢
        obtain ⟨ν', hP', hν'⟩ := hg0
        refine ⟨ν', hP', fun b => ?_⟩
        rw [hD, hν' a, ← sub_smul, map_smul, hν' b, smul_comm]
      have hwt : ∀ b, T b b ((((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x)
          = ((μ b : ℝ) : ℂ) • ((((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x) := by
        intro b
        rw [map_smul, hx b, smul_comm]
      have hz := ih (l'.map D) (by simpa using hl') hgood _ hwt (by rw [← h1, h3])
      exact (smul_eq_zero.mp hz).resolve_left hc0

theorem vc_eq_zero_of_mem_span (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop)
    {μ : Fin n → ℝ} (hμ : ¬ P μ) {x : U} (hx : ∀ a, T a a x = ((μ a : ℝ) : ℂ) • x)
    (hxs : x ∈ Submodule.span ℂ (vcGood T P)) : x = 0 := by
  obtain ⟨l, hl, e⟩ := vc_exists_list (fun w hw c => vcGood_smul T P hw c) hxs
  exact vc_eq_zero_of_list T P hμ l.length l rfl hl x hx e

def vcMon (T : Fin n → Fin n → Module.End ℂ U) (v : U) : ℕ → Set U
  | 0 => {v}
  | k + 1 => {y | ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, y = T a b x}

def vcMonAll (T : Fin n → Fin n → Module.End ℂ U) (v : U) : Set U := ⋃ k, vcMon T v k

def vcHt (β : Fin n → ℝ) : ℝ := ∑ a : Fin n, -((a : ℕ) : ℝ) * β a

theorem vcHt_add (β γ : Fin n → ℝ) : vcHt (β + γ) = vcHt β + vcHt γ := by
  simp only [vcHt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem vcHt_zero : vcHt (0 : Fin n → ℝ) = 0 := by
  simp [vcHt]

theorem vcHt_root {c d : Fin n} (h : c < d) : 1 ≤ vcHt (root c d) := by
  have h1 : ∀ e : Fin n, ∑ a : Fin n, -((a : ℕ) : ℝ) * (Pi.single e (1 : ℝ) : Fin n → ℝ) a
      = -((e : ℕ) : ℝ) := by
    intro e
    rw [Fintype.sum_eq_single e (fun a ha => by simp [Pi.single_apply, ha])]
    simp
  have key : vcHt (root c d) = ((d : ℕ) : ℝ) - ((c : ℕ) : ℝ) := by
    simp only [vcHt, root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, h1]
    ring
  rw [key]
  have h' : (c : ℕ) + 1 ≤ (d : ℕ) := h
  have h'' : ((c : ℕ) : ℝ) + 1 ≤ ((d : ℕ) : ℝ) := by exact_mod_cast h'
  linarith

theorem vc_inRootCone_zero' : InRootCone (0 : Fin n → ℝ) := by
  unfold InRootCone
  exact ⟨fun _ _ => 0, by simp⟩

theorem vc_inRootCone_add_root {β : Fin n → ℝ} (hβ : InRootCone β) {c d : Fin n} (h : c < d) :
    InRootCone (β + root c d) := by
  unfold InRootCone at hβ ⊢
  obtain ⟨m, hm⟩ := hβ
  refine ⟨fun a b => m a b + if a = c ∧ b = d then 1 else 0, ?_⟩
  have hsplit : ∀ a b : Fin n,
      (if a < b then (((m a b + if a = c ∧ b = d then 1 else 0 : ℕ)) : ℝ) • root a b else 0)
        = (if a < b then (m a b : ℝ) • root a b else 0)
          + (if a = c ∧ b = d then root c d else 0) := by
    intro a b
    by_cases hab : a = c ∧ b = d
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h, add_smul]
    · rw [if_neg hab, if_neg hab]
      simp
  have hind : (∑ a : Fin n, ∑ b : Fin n, (if a = c ∧ b = d then root c d else 0)) = root c d := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [hm]
  simp only [hsplit, Finset.sum_add_distrib, hind]

theorem vcMon_weight (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) {v : U}
    {base : Fin n → ℝ} (hv : ∀ a, T a a v = ((base a : ℝ) : ℂ) • v) :
    ∀ k, ∀ w ∈ vcMon T v k, ∃ ν : Fin n → ℝ, (∀ a, T a a w = ((ν a : ℝ) : ℂ) • w) ∧
      InRootCone (ν - base) ∧ (k : ℝ) ≤ vcHt (ν - base) := by
  have hz : ∀ w, w ∈ vcMon T v 0 → w = v := fun w hw => hw
  have hs : ∀ k w, w ∈ vcMon T v (k + 1) → ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, w = T a b x :=
    fun k w hw => hw
  intro k
  induction k with
  | zero =>
    intro w hw
    rw [hz w hw]
    refine ⟨base, hv, ?_, ?_⟩
    · rw [sub_self]
      exact vc_inRootCone_zero'
    · rw [sub_self, vcHt_zero]
      simp
  | succ k ih =>
    intro w hw
    obtain ⟨a, b, hab', x, hx, rfl⟩ := hs k w hw
    obtain ⟨ν, hxν, hcone, hht⟩ := ih x hx
    have hab : a ≠ b := ne_of_lt hab'
    have hw : ∀ c, T c c (T a b x) = (((ν + root a b) c : ℝ) : ℂ) • T a b x := by
      intro c
      have hc := LinearMap.congr_fun (hT c c a b) x
      have e : (T c c * T a b - T a b * T c c) x = T c c (T a b x) - T a b (T c c x) := by
        first
          | rfl
          | simp [LinearMap.sub_apply, Module.End.mul_apply]
          | simp [LinearMap.sub_apply, LinearMap.mul_apply]
      rw [e, hxν c, map_smul] at hc
      simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : c = a
      · have h2 : ¬ b = c := by
          rw [h1]
          exact fun h => hab h.symm
        rw [if_pos h1, if_neg h2, sub_zero] at hc
        rw [h1] at hc ⊢
        rw [if_pos rfl, if_neg hab, sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul,
          one_smul]
        rw [sub_eq_iff_eq_add] at hc
        rw [hc, add_comm]
      · by_cases h3 : c = b
        · have h2 : b = c := h3.symm
          rw [if_neg h1, if_pos h2, zero_sub] at hc
          rw [h3] at hc ⊢
          rw [if_neg (Ne.symm hab), if_pos rfl, zero_sub, ← sub_eq_add_neg, Complex.ofReal_sub,
            Complex.ofReal_one, sub_smul, one_smul]
          rw [LinearMap.neg_apply, sub_eq_iff_eq_add] at hc
          rw [hc, neg_add_eq_sub]
        · have h2 : ¬ b = c := fun h => h3 h.symm
          rw [if_neg h1, if_neg h2, sub_zero, LinearMap.zero_apply, sub_eq_zero] at hc
          rw [if_neg h1, if_neg h3, sub_zero, add_zero, hc]
    have e : ν + root a b - base = (ν - base) + root a b := by abel
    refine ⟨ν + root a b, hw, ?_, ?_⟩
    · rw [e]
      exact vc_inRootCone_add_root hcone hab'
    · rw [e, vcHt_add]
      have := vcHt_root hab'
      push_cast
      linarith

theorem vc_sup_stable {G : Set U} {F : Submodule ℂ U} (X : Module.End ℂ U)
    (hG : ∀ w ∈ G, X w ∈ Submodule.span ℂ G ⊔ F) (hF : ∀ x ∈ F, X x ∈ F) :
    ∀ x ∈ Submodule.span ℂ G ⊔ F, X x ∈ Submodule.span ℂ G ⊔ F := by
  intro x hx
  have h : Submodule.span ℂ G ⊔ F ≤ (Submodule.span ℂ G ⊔ F).comap X := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro w hw
      exact hG w hw
    · intro y hy
      exact Submodule.mem_sup_right (hF y hy)
  exact h hx

theorem vc_genSub_le_mon (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) (v : U)
    (F : Submodule ℂ U) (hF : ∀ a b, ∀ x ∈ F, T a b x ∈ F) (hlow : ∀ a b, b < a → T a b v ∈ F)
    (hdiag : ∀ a, ∃ c : ℂ, T a a v = c • v) :
    genSub T (Submodule.span ℂ {v}) ≤ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
  have hz : ∀ w, w ∈ vcMon T v 0 → w = v := fun w hw => hw
  have hv0 : v ∈ vcMon T v 0 := by
    show v ∈ ({v} : Set U)
    exact Set.mem_singleton v
  have hs : ∀ k w, w ∈ vcMon T v (k + 1) → ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, w = T a b x :=
    fun k w hw => hw
  have hn : ∀ k a b, a < b → ∀ x ∈ vcMon T v k, T a b x ∈ vcMon T v (k + 1) := by
    intro k a b hab x hx
    show ∃ a' b', a' < b' ∧ ∃ y ∈ vcMon T v k, T a b x = T a' b' y
    exact ⟨a, b, hab, x, hx, rfl⟩
  have hmon : ∀ k, ∀ w ∈ vcMon T v k, w ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro k w hw
    refine Submodule.mem_sup_left (Submodule.subset_span ?_)
    show w ∈ ⋃ k, vcMon T v k
    exact Set.mem_iUnion.mpr ⟨k, hw⟩
  have hup : ∀ c d, c < d → ∀ y ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F,
      T c d y ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro c d hcd
    refine vc_sup_stable (T c d) ?_ (hF c d)
    intro w hw
    obtain ⟨k, hk⟩ : ∃ k, w ∈ vcMon T v k := by simpa [vcMonAll] using hw
    exact hmon (k + 1) _ (hn k c d hcd w hk)
  have hstab : ∀ k, ∀ a b, ∀ w ∈ vcMon T v k,
      T a b w ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro k
    induction k with
    | zero =>
      intro a b w hw
      rw [hz w hw]
      rcases lt_trichotomy a b with h | h | h
      · exact hmon 1 _ (hn 0 a b h v hv0)
      · rw [h]
        obtain ⟨c, hc⟩ := hdiag b
        rw [hc]
        exact Submodule.smul_mem _ c (hmon 0 v hv0)
      · exact Submodule.mem_sup_right (hlow a b h)
    | succ k ih =>
      intro a b w hw
      obtain ⟨c, d, hcd, x, hx, rfl⟩ := hs k w hw
      have hc := LinearMap.congr_fun (hT a b c d) x
      have e : (T a b * T c d - T c d * T a b) x = T a b (T c d x) - T c d (T a b x) := by
        first
          | rfl
          | simp [LinearMap.sub_apply, Module.End.mul_apply]
          | simp [LinearMap.sub_apply, LinearMap.mul_apply]
      rw [e, sub_eq_iff_eq_add] at hc
      rw [hc]
      refine Submodule.add_mem _ ?_ (hup c d hcd _ (ih a b x hx))
      rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs
        · exact ih a d x hx
        · rw [LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · split_ifs
        · exact ih c b x hx
        · rw [LinearMap.zero_apply]
          exact Submodule.zero_mem _
  refine vc_genSub_le T (Submodule.span ℂ {v}) _ ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmon 0 v hv0
  · intro a b y hy
    refine vc_sup_stable (T a b) ?_ (hF a b) y hy
    intro w hw
    obtain ⟨k, hk⟩ : ∃ k, w ∈ vcMon T v k := by simpa [vcMonAll] using hw
    exact hstab k a b w hk

def vcIter (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) : ℕ → Module.End ℂ U
  | 0 => 1
  | i + 1 => (A - θ (k0 + i) • 1) * vcIter A θ k0 i

theorem vcIter_maps (A : Module.End ℂ U) (θ : ℕ → ℂ) (F : ℕ → Submodule ℂ U)
    (hstep : ∀ k, ∀ x ∈ F k, A x - θ k • x ∈ F (k + 1)) (k0 : ℕ) :
    ∀ i, ∀ x ∈ F k0, vcIter A θ k0 i x ∈ F (k0 + i)
  | 0, x, hx => by simpa [vcIter] using hx
  | i + 1, x, hx => by
    have h := hstep (k0 + i) _ (vcIter_maps A θ F hstep k0 i x hx)
    simpa [vcIter, Module.End.mul_apply, LinearMap.sub_apply, add_assoc] using h

theorem vcIter_eig (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) {x : U} {t : ℂ} (hx : A x = t • x) :
    ∀ i, vcIter A θ k0 i x = (∏ i' ∈ range i, (t - θ (k0 + i'))) • x
  | 0 => by simp [vcIter]
  | i + 1 => by
    rw [vcIter, Module.End.mul_apply, vcIter_eig A θ k0 hx i, Finset.prod_range_succ]
    simp only [map_smul, LinearMap.sub_apply, hx, LinearMap.smul_apply, Module.End.one_apply]
    rw [← sub_smul, smul_smul, mul_comm]

theorem vcIter_comm (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) {X : Module.End ℂ U} (hX : Commute A X) :
    ∀ i, Commute (vcIter A θ k0 i) X
  | 0 => Commute.one_left X
  | i + 1 => ((hX.sub_left ((Commute.one_left X).smul_left _)).mul_left (vcIter_comm A θ k0 hX i))

end Core

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Core2

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]

theorem vc_cone_core (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) (A : Module.End ℂ U)
    (hA : ∀ a b, Commute A (T a b)) (F : ℕ → Submodule ℂ U) (θ : ℕ → ℂ)
    (hF : ∀ k a b, ∀ x ∈ F k, T a b x ∈ F k)
    (hstep : ∀ k, ∀ x ∈ F k, A x - θ k • x ∈ F (k + 1))
    (m j : ℕ) (h0 : F 0 = ⊤) (hm : F m = ⊥) (hj : j < m) (hθ : ∀ k < m, k ≠ j → θ k ≠ θ j)
    (v : U) (base : Fin n → ℝ) (hFj : F j ≤ genSub T (Submodule.span ℂ {v}) ⊔ F (j + 1))
    (hlow : ∀ a b, b < a → T a b v ∈ F (j + 1)) (hdiag : ∀ a, T a a v = ((base a : ℝ) : ℂ) • v) :
    (∀ (μ : Fin n → ℝ) (x : U), A x = θ j • x → x ≠ 0 → (∀ a, T a a x = ((μ a : ℝ) : ℂ) • x) →
        InRootCone (μ - base)) ∧
    ∀ x₁ x₂ : U, A x₁ = θ j • x₁ → A x₂ = θ j • x₂ →
      (∀ a, T a a x₁ = ((base a : ℝ) : ℂ) • x₁) → (∀ a, T a a x₂ = ((base a : ℝ) : ℂ) • x₂) →
      ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • x₁ + c₂ • x₂ = 0 := by
  set post := vcIter A θ (j + 1) (m - j - 1) with hpost
  set c' : ℂ := ∏ i ∈ range (m - j - 1), (θ j - θ (j + 1 + i)) with hc'
  have hc'0 : c' ≠ 0 := by
    rw [hc', Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    exact sub_ne_zero.mpr (hθ (j + 1 + i) (by omega) (by omega)).symm
  have hpostT : ∀ a b, Commute post (T a b) := fun a b => vcIter_comm A θ _ (hA a b) _
  have hred : ∀ x, A x = θ j • x → ∃ y ∈ Submodule.span ℂ (vcMonAll T v), post y = c' • x := by
    intro x hx
    have hxj : x ∈ F j := by
      have h1 := vcIter_maps A θ F hstep 0 j x (by rw [h0]; exact Submodule.mem_top)
      rw [vcIter_eig A θ 0 hx j, Nat.zero_add] at h1
      have hc : (∏ i' ∈ range j, (θ j - θ (0 + i'))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        exact sub_ne_zero.mpr (hθ (0 + i) (by omega) (by omega)).symm
      have := (F j).smul_mem (∏ i' ∈ range j, (θ j - θ (0 + i')))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hx2 : x ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F (j + 1) := by
      have h3 := vc_genSub_le_mon T hT v (F (j + 1)) (hF (j + 1)) hlow (fun a => ⟨_, hdiag a⟩)
      exact (sup_le h3 le_sup_right) (hFj hxj)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
    refine ⟨y, hy, ?_⟩
    have hpz : post z = 0 := by
      have := vcIter_maps A θ F hstep (j + 1) (m - j - 1) z hz
      rw [show j + 1 + (m - j - 1) = m by omega, hm] at this
      exact (Submodule.mem_bot ℂ).mp this
    have hpx : post x = c' • x := vcIter_eig A θ (j + 1) hx _
    rw [← hpx, ← hyz, map_add, hpz, add_zero]
  have hpostGood : ∀ (P : (Fin n → ℝ) → Prop) (w : U), w ∈ vcGood T P → post w ∈ vcGood T P := by
    intro P w ⟨ν, hP, hν⟩
    refine ⟨ν, hP, fun a => ?_⟩
    rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hν a, map_smul]
  have hspanGood : ∀ (P : (Fin n → ℝ) → Prop) (G : Set U), G ⊆ vcGood T P →
      ∀ y ∈ Submodule.span ℂ G, post y ∈ Submodule.span ℂ (vcGood T P) := by
    intro P G hG y hy
    have : Submodule.span ℂ G ≤ (Submodule.span ℂ (vcGood T P)).comap post :=
      Submodule.span_le.mpr (fun w hw => Submodule.subset_span (hpostGood P w (hG hw)))
    exact this hy
  refine ⟨?_, ?_⟩
  · intro μ x hx hx0 hμ
    by_contra hcone
    obtain ⟨y, hy, hyx⟩ := hred x hx
    have hmon : vcMonAll T v ⊆ vcGood T (fun ν => InRootCone (ν - base)) := by
      intro w hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      obtain ⟨ν, hν, hc, _⟩ := vcMon_weight T hT hdiag k w hk
      exact ⟨ν, hc, hν⟩
    have hs := hspanGood _ _ hmon y hy
    rw [hyx] at hs
    have hz := vc_eq_zero_of_mem_span T (fun ν => InRootCone (ν - base)) hcone
      (x := c' • x) (fun a => by rw [map_smul, hμ a, smul_comm]) hs
    exact hx0 ((smul_eq_zero.mp hz).resolve_left hc'0)
  · have hpv : ∀ a, T a a (post v) = ((base a : ℝ) : ℂ) • post v := by
      intro a
      rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hdiag a, map_smul]
    have hvert : ∀ x, A x = θ j • x → (∀ a, T a a x = ((base a : ℝ) : ℂ) • x) →
        ∃ β : ℂ, x = β • post v := by
      intro x hx hxw
      obtain ⟨y, hy, hyx⟩ := hred x hx
      have hmon : vcMonAll T v ⊆
          (Submodule.span ℂ {v} ⊔ Submodule.span ℂ (vcGood T (fun ν => ν ≠ base)) : Submodule ℂ U) := by
        intro w hw
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
        rcases k with _ | k
        · have hwv : w = v := hk
          subst hwv
          exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)
        · obtain ⟨ν, hν, _, hht⟩ := vcMon_weight T hT hdiag (k + 1) w hk
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨ν, ?_, hν⟩)
          intro hνb
          rw [hνb, sub_self, vcHt_zero] at hht
          push_cast at hht
          linarith
      have hy2 := (Submodule.span_le.mpr hmon) hy
      obtain ⟨y1, hy1, r, hr, hyr⟩ := Submodule.mem_sup.mp hy2
      obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hy1
      have hpr := hspanGood (fun ν => ν ≠ base) _ (Set.Subset.refl _) r hr
      have hd : c' • x - α • post v = post r := by
        rw [← hyx, ← hyr, map_add, map_smul]
        abel
      have hdw : ∀ a, T a a (c' • x - α • post v) = ((base a : ℝ) : ℂ) • (c' • x - α • post v) := by
        intro a
        rw [map_sub, map_smul, map_smul, hxw a, hpv a, smul_sub, smul_comm c', smul_comm α]
      have hd0 := vc_eq_zero_of_mem_span T (fun ν => ν ≠ base) (μ := base) (by simp) hdw
        (by rw [hd]; exact hpr)
      refine ⟨c'⁻¹ * α, ?_⟩
      rw [sub_eq_zero] at hd0
      rw [mul_smul, ← hd0, smul_smul, inv_mul_cancel₀ hc'0, one_smul]
    intro x₁ x₂ h1 h2 hw1 hw2
    obtain ⟨β₁, rfl⟩ := hvert x₁ h1 hw1
    obtain ⟨β₂, rfl⟩ := hvert x₂ h2 hw2
    by_cases hb : β₁ = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hb]⟩
    · refine ⟨β₂, -β₁, Or.inr (neg_ne_zero.mpr hb), ?_⟩
      rw [smul_smul, smul_smul, mul_comm β₂ β₁, neg_mul, neg_smul, add_neg_cancel]

def vcFlag (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ) (k : ℕ) : Submodule ℂ U :=
  genSub T (Submodule.span ℂ (g '' {t | k ≤ r t}))

variable (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ)

theorem vcFlag_stable (k : ℕ) (a b : Fin n) : ∀ x ∈ vcFlag T g r k, T a b x ∈ vcFlag T g r k :=
  fun _ hx => vc_genSub_stable T _ a b hx

theorem vcFlag_gen {t : Fin n} {k : ℕ} (h : k ≤ r t) : g t ∈ vcFlag T g r k :=
  vc_le_genSub T _ (Submodule.subset_span ⟨t, h, rfl⟩)

theorem vcFlag_anti {k l : ℕ} (h : k ≤ l) : vcFlag T g r l ≤ vcFlag T g r k :=
  vc_genSub_le T _ _ (Submodule.span_le.mpr (by
    rintro _ ⟨t, ht, rfl⟩
    exact vcFlag_gen T g r (le_trans h ht))) (vcFlag_stable T g r k)

theorem vcFlag_eq_bot {m : ℕ} (hm : ∀ t, r t < m) : vcFlag T g r m = ⊥ := by
  refine le_bot_iff.mp (vc_genSub_le T _ ⊥ ?_ (fun a b v hv => by
    rw [(Submodule.mem_bot ℂ).mp hv, map_zero]; exact Submodule.zero_mem _))
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  exact absurd ht (not_le.mpr (hm t))

theorem vcFlag_step (A : Module.End ℂ U) (hA : ∀ a b, Commute A (T a b)) (θ : ℕ → ℂ)
    (hgen : ∀ t, A (g t) - θ (r t) • g t ∈ vcFlag T g r (r t + 1)) :
    ∀ k, ∀ x ∈ vcFlag T g r k, A x - θ k • x ∈ vcFlag T g r (k + 1) := by
  have hAst : ∀ k, ∀ x ∈ vcFlag T g r k, A x ∈ vcFlag T g r k := by
    intro k
    let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r k).comap A
    have hle : vcFlag T g r k ≤ S := by
      refine vc_genSub_le T _ S ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨vcFlag_gen T g r ht, ?_⟩
        show A (g t) ∈ vcFlag T g r k
        have h1 := vcFlag_anti T g r (show k ≤ r t + 1 by simp at ht; omega) (hgen t)
        have h2 := (vcFlag T g r k).smul_mem (θ (r t)) (vcFlag_gen T g r ht)
        simpa using (vcFlag T g r k).add_mem h1 h2
      · intro a b x hx
        refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
        show A (T a b x) ∈ vcFlag T g r k
        rw [← Module.End.mul_apply, (hA a b).eq, Module.End.mul_apply]
        exact vcFlag_stable T g r k a b _ hx.2
    exact fun x hx => (hle hx).2
  intro k
  let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r (k + 1)).comap (A - θ k • 1)
  have hle : vcFlag T g r k ≤ S := by
    refine vc_genSub_le T _ S ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨vcFlag_gen T g r ht, ?_⟩
      show (A - θ k • 1) (g t) ∈ vcFlag T g r (k + 1)
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      have ht' : k ≤ r t := ht
      rcases eq_or_lt_of_le ht' with h | h
      · rw [h]; exact hgen t
      · have hg : g t ∈ vcFlag T g r (k + 1) := vcFlag_gen T g r h
        exact Submodule.sub_mem _ (hAst (k + 1) _ hg) (Submodule.smul_mem _ _ hg)
    · intro a b x hx
      refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
      show (A - θ k • 1) (T a b x) ∈ vcFlag T g r (k + 1)
      have hc : Commute (A - θ k • 1) (T a b) := (hA a b).sub_left ((Commute.one_left _).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      exact vcFlag_stable T g r (k + 1) a b _ hx.2
  intro x hx
  have := (hle hx).2
  simpa using this

theorem vcFlag_top_le {j : ℕ} {s : Fin n} (hr : Function.Injective r) (hj : r s = j) :
    vcFlag T g r j ≤ genSub T (Submodule.span ℂ {g s}) ⊔ vcFlag T g r (j + 1) := by
  refine vc_genSub_le T _ _ ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : j ≤ r t := ht
    rcases eq_or_lt_of_le ht' with h | h
    · have hts : t = s := hr (by omega)
      subst hts
      exact Submodule.mem_sup_left (vc_le_genSub T _ (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (vcFlag_gen T g r h)
  · intro a b x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (vc_genSub_stable T _ a b hy) (vcFlag_stable T g r _ a b z hz)

end Core2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.add_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp_all

theorem vc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  simp only [tensVd, prj, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.sub_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp_all

theorem vc_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem vc_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem vc_eeV_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeV E (Pi.single t m) e = E t e m := by
  simp [eeV, prj, Pi.single_apply, apply_ite]

theorem vc_eeVd_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeVd E (Pi.single t m) e = -E e t m := by
  simp [eeVd, prj, Pi.single_apply, apply_ite]

theorem vc_commV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeV E) (tensV E a b) := by
  obtain ⟨hT, -, hcas, -⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeV E g =
      casimir (tensV E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensV E a b g c)) = tensV E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensV_apply, vc_tensV_apply, map_add]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeV E * tensV E a b = tensV E a b * eeV E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeV E (tensV E a b g) = (2 : ℂ) • tensV E a b (eeV E g) := by
    rw [← map_smul (tensV E a b) (2 : ℂ) (eeV E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensV E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_commVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeVd E) (tensVd E a b) := by
  obtain ⟨-, hT, -, hcas⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeVd E g =
      casimir (tensVd E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensVd E a b g c)) = tensVd E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensVd_apply, vc_tensVd_apply, map_sub]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeVd E * tensVd E a b = tensVd E a b * eeVd E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeVd E (tensVd E a b g) = (2 : ℂ) • tensVd E a b (eeVd E g) := by
    rw [← map_smul (tensVd E a b) (2 : ℂ) (eeVd E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensVd E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (G : Submodule ℂ (Fin n → M)) (hG : ∀ a b, ∀ x ∈ G, T a b x ∈ G)
    (hφ : ∀ c, (Pi.single c φ : Fin n → M) ∈ G) : G = ⊤ := by
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [Pi.single_smul']
        exact G.smul_mem r (hx c) }
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (hG a b _ (hm c))
    simpa using h2
  have hle := vc_genSub_le E _ S (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ) hSS
  rw [hgen] at hle
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

end Inst

section Inst2

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_genV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      ∑ d ∈ univ.filter (fun d => t < d), tensV E t d (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeV_single, Finset.sum_apply]
  simp only [vc_tensV_single, Pi.add_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, hlow t e h, not_lt.mpr h.le]
  · have hc : (univ.filter fun d : Fin n => e < d).card = n - 1 - e := by
      rw [filter_lt_eq_Ioi, Fin.card_Ioi]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_add, hc, hd]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have he : 1 + (e : ℕ) ≤ n := by have := e.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub he]
    simp only [rho, thV]
    push_cast
    ring
  · simp [h.ne', h]

theorem vc_genVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      -∑ d ∈ univ.filter (fun d => d < t), tensVd E d t (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeVd_single, Pi.neg_apply, Finset.sum_apply]
  simp only [vc_tensVd_single, Pi.sub_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, h]
  · have hc : (univ.filter fun d : Fin n => d < e).card = e := by
      rw [filter_gt_eq_Iio, Fin.card_Iio]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_sub, hc, hd,
      neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · simp [h.ne', hlow e t h, not_lt.mpr h.le]

end Inst2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst3

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def vcSgl (φ : M) : Fin n → Fin n → M := fun t => Pi.single t φ

def vcRV (n : ℕ) : Fin n → ℕ := fun t => (t : ℕ)

def vcRVd (n : ℕ) : Fin n → ℕ := fun t => (Fin.rev t : ℕ)

def vcThV (lam : Fin n → ℝ) : ℕ → ℂ := fun k => if h : k < n then ((thV lam ⟨k, h⟩ : ℝ) : ℂ) else 0

def vcThVd (lam : Fin n → ℝ) : ℕ → ℂ :=
  fun k => if h : k < n then ((thVd lam (Fin.rev ⟨k, h⟩) : ℝ) : ℂ) else 0

theorem vcThV_rV (lam : Fin n → ℝ) (t : Fin n) : vcThV lam (vcRV n t) = ((thV lam t : ℝ) : ℂ) := by
  simp [vcThV, vcRV, t.isLt]

theorem vcThVd_rVd (lam : Fin n → ℝ) (t : Fin n) : vcThVd lam (vcRVd n t) = ((thVd lam t : ℝ) : ℂ) := by
  unfold vcThVd vcRVd
  rw [dif_pos (Fin.rev t).isLt]
  simp only [Fin.eta, Fin.rev_rev]

theorem vcThV_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRV n s → vcThV lam k ≠ vcThV lam (vcRV n s) := by
  intro k hk hks heq
  rw [vcThV_rV, show vcThV lam k = ((thV lam ⟨k, hk⟩ : ℝ) : ℂ) by simp [vcThV, hk]] at heq
  have h1 : thV lam ⟨k, hk⟩ = thV lam s := by exact_mod_cast heq
  have h2 : lam ⟨k, hk⟩ = lam s := by unfold thV at h1; linarith
  exact hks (congrArg Fin.val (hanti.injective h2))

theorem vcThVd_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRVd n s → vcThVd lam k ≠ vcThVd lam (vcRVd n s) := by
  intro k hk hks heq
  rw [vcThVd_rVd, show vcThVd lam k = ((thVd lam (Fin.rev ⟨k, hk⟩) : ℝ) : ℂ) by simp [vcThVd, hk]] at heq
  have h1 : thVd lam (Fin.rev ⟨k, hk⟩) = thVd lam s := by exact_mod_cast heq
  have h2 : lam (Fin.rev ⟨k, hk⟩) = lam s := by unfold thVd at h1; linarith
  have h3 := hanti.injective h2
  apply hks
  rw [← h3]
  simp [vcRVd]

theorem vc_xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M}
    (hf : f ∈ Xs A S θ) : A f = ((θ : ℝ) : ℂ) • f := by
  have h := (Submodule.mem_inf.mp hf).2
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

end Inst3

theorem verma_cone (n : ℕ) : VermaConeStatement n := by
  intro M _ _ E lam φ s hE hlow hd hgen hanti
  obtain ⟨hTV, hTVd, -, -⟩ := tens_statement n M E hE
  refine ⟨?_, ?_⟩
  · have hgenV : ∀ t, eeV E (vcSgl φ t) - vcThV lam (vcRV n t) • vcSgl φ t ∈
        vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n t + 1) := by
      intro t
      rw [vcThV_rV]
      show eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genV E lam φ hlow hd t]
      refine Submodule.sum_mem _ fun d hd' => vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      exact hd'
    have h0 : vcFlag (tensV E) (vcSgl φ) (vcRV n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensV E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensV E) (vcSgl φ) (vcRV n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensV_single]
      split_ifs
      · have hx : (Pi.single a m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨a, rfl⟩
        simpa using Submodule.neg_mem _ hx
      · simp
    have hlowV : ∀ a b, b < a → tensV E a b (vcSgl φ s) ∈ vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n s + 1) := by
      intro a b hab
      show tensV E a b (Pi.single s φ) ∈ _
      rw [vc_tensV_single, hlow a b hab, Pi.single_zero, zero_add]
      split_ifs with hbs
      · subst hbs
        exact vcFlag_gen _ _ _ hab
      · exact Submodule.zero_mem _
    have hdiagV : ∀ a, tensV E a a (vcSgl φ s) = (((lam + rho n + Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensV E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensV_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul]
      · simp [has, Pi.single_apply]
    have hrinj : Function.Injective (vcRV n) := fun a b h => Fin.ext h
    obtain ⟨h1, h2⟩ := vc_cone_core (tensV E) hTV (eeV E) (vc_commV E hE) (vcFlag (tensV E) (vcSgl φ) (vcRV n))
      (vcThV lam) (vcFlag_stable _ _ _) (vcFlag_step _ _ _ (eeV E) (vc_commV E hE) (vcThV lam) hgenV) n
      (vcRV n s) h0 (vcFlag_eq_bot _ _ _ (fun t => t.isLt)) s.isLt (vcThV_ne lam hanti s) (vcSgl φ s)
      (lam + rho n + Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowV hdiagV
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThV_rV]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThV_rV]; exact vc_xs hf₁) (by rw [vcThV_rV]; exact vc_xs hf₂) hw₁ hw₂
  · have hgenVd : ∀ t, eeVd E (vcSgl φ t) - vcThVd lam (vcRVd n t) • vcSgl φ t ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n t + 1) := by
      intro t
      rw [vcThVd_rVd]
      show eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genVd E lam φ hlow hd t]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd' =>
        vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      have := Fin.lt_def.mp hd'
      simp only [vcRVd, Fin.val_rev]
      omega
    have h0 : vcFlag (tensVd E) (vcSgl φ) (vcRVd n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensVd E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensVd E) (vcSgl φ) (vcRVd n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensVd_single]
      split_ifs
      · have hx : (Pi.single b m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨b, rfl⟩
        simpa using hx
      · simp
    have hlowVd : ∀ a b, b < a → tensVd E a b (vcSgl φ s) ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n s + 1) := by
      intro a b hab
      show tensVd E a b (Pi.single s φ) ∈ _
      rw [vc_tensVd_single, hlow a b hab, Pi.single_zero, zero_sub]
      split_ifs with has
      · subst has
        refine Submodule.neg_mem _ (vcFlag_gen _ _ _ ?_)
        have := Fin.lt_def.mp hab
        simp only [vcRVd, Fin.val_rev]
        omega
      · simp
    have hdiagVd : ∀ a, tensVd E a a (vcSgl φ s) =
        (((lam + rho n - Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensVd E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensVd_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul, sub_smul]
      · simp [has, Pi.single_apply]
    have hrinj : Function.Injective (vcRVd n) := fun a b h => Fin.rev_injective (Fin.ext h)
    obtain ⟨h1, h2⟩ := vc_cone_core (tensVd E) hTVd (eeVd E) (vc_commVd E hE)
      (vcFlag (tensVd E) (vcSgl φ) (vcRVd n)) (vcThVd lam) (vcFlag_stable _ _ _)
      (vcFlag_step _ _ _ (eeVd E) (vc_commVd E hE) (vcThVd lam) hgenVd) n
      (vcRVd n s) h0 (vcFlag_eq_bot _ _ _ (fun t => (Fin.rev t).isLt)) (Fin.rev s).isLt
      (vcThVd_ne lam hanti s) (vcSgl φ s)
      (lam + rho n - Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowVd hdiagVd
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThVd_rVd]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThVd_rVd]; exact vc_xs hf₁) (by rw [vcThVd_rVd]; exact vc_xs hf₂) hw₁ hw₂

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section VK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem vk_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem vk_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem vk_eeV_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem vk_eeVd_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem vk_rel (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b c d : Fin n) (x : M) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  have h := LinearMap.congr_fun (hE a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero] at h ⊢) <;>
    (rw [sub_eq_iff_eq_add] at h; rw [h]; abel)

theorem vk_eeV_comm (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    eeV E * tensV E a b = tensV E a b * eeV E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  simp only [Module.End.mul_apply, vk_eeV_apply]
  have h1 : ∀ c, E c d (tensV E a b f c) = E a b (E c d (f c)) + (if d = a then E c b (f c) else 0) -
      (if b = c then E a d (f c) else 0) + (if c = a then E a d (f b) else 0) := by
    intro c
    rw [vk_tensV_apply, map_add, vk_rel E hE c d a b]
    by_cases h : c = a
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  simp only [vk_tensV_apply, vk_eeV_apply, map_sum]
  by_cases hda : d = a
  · subst hda; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [hda, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem vk_eeVd_comm (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    eeVd E * tensVd E a b = tensVd E a b * eeVd E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  simp only [Module.End.mul_apply, vk_eeVd_apply]
  have h1 : ∀ c, E d c (tensVd E a b f c) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) -
      (if b = d then E a c (f c) else 0) - (if c = b then E d b (f a) else 0) := by
    intro c
    rw [vk_tensVd_apply, map_sub, vk_rel E hE d c a b]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  simp only [vk_tensVd_apply, vk_eeVd_apply, map_sum, map_neg]
  by_cases hdb : d = b
  · subst hdb
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    abel
  · have hbd : ¬ b = d := fun h => hdb h.symm
    simp [hdb, hbd, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']

end VK

section GenKill

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem vk_le_genSub (T : Fin n → Fin n → Module.End ℂ W) (S : Submodule ℂ W) : S ≤ genSub T S :=
  le_sInf fun _ hT => hT.1

theorem vk_genSub_stable (T : Fin n → Fin n → Module.End ℂ W) (S : Submodule ℂ W) (a b : Fin n) (v : W)
    (hv : v ∈ genSub T S) : T a b v ∈ genSub T S := by
  rw [genSub, Submodule.mem_sInf] at hv ⊢
  intro P hP
  exact hP.2 a b v (hv P hP)

theorem vk_genSub_mono (T : Fin n → Fin n → Module.End ℂ W) {S S' : Submodule ℂ W} (h : S ≤ S') :
    genSub T S ≤ genSub T S' :=
  sInf_le ⟨h.trans (vk_le_genSub T S'), fun a b v hv => vk_genSub_stable T S' a b v hv⟩

theorem vk_genSub_map (T : Fin n → Fin n → Module.End ℂ W) (B : Module.End ℂ W)
    (hB : ∀ a b, B * T a b = T a b * B) (P : Submodule ℂ W) (hP : ∀ a b, ∀ v ∈ P, T a b v ∈ P)
    (S : Set W) (hS : ∀ x ∈ S, B x ∈ P) : ∀ x ∈ genSub T (Submodule.span ℂ S), B x ∈ P := by
  intro x hx
  have hle : genSub T (Submodule.span ℂ S) ≤ P.comap B := by
    refine sInf_le ⟨Submodule.span_le.mpr fun y hy => hS y hy, fun a b v hv => ?_⟩
    rw [Submodule.mem_comap] at hv ⊢
    rw [← Module.End.mul_apply, hB a b, Module.End.mul_apply]
    exact hP a b _ hv
  exact hle hx

theorem vk_shift_comm (T : Fin n → Fin n → Module.End ℂ W) (A : Module.End ℂ W)
    (hAT : ∀ a b, A * T a b = T a b * A) (c : ℂ) (a b : Fin n) :
    (A - c • 1) * T a b = T a b * (A - c • 1) := by
  rw [sub_mul, mul_sub, hAT, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem vk_aeval_lin (A : Module.End ℂ W) (c : ℂ) : aeval A (X - C c) = A - c • 1 := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem vk_kill (T : Fin n → Fin n → Module.End ℂ W) (A : Module.End ℂ W)
    (hAT : ∀ a b, A * T a b = T a b * A) (θ : Fin n → ℂ) (g : Fin n → W)
    (hstep : ∀ t, (A - θ t • 1) (g t) ∈ genSub T (Submodule.span ℂ (g '' {d | t < d}))) :
    ∀ x ∈ genSub T (Submodule.span ℂ (Set.range g)), aeval A (∏ t, (X - C (θ t))) x = 0 := by
  have main : ∀ m k : ℕ, n ≤ k + m →
      ∀ x ∈ genSub T (Submodule.span ℂ (g '' {d : Fin n | k ≤ (d : ℕ)})),
        aeval A (∏ t ∈ univ.filter (fun d : Fin n => k ≤ (d : ℕ)), (X - C (θ t))) x = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk x hx
      have hempty : g '' {d : Fin n | k ≤ (d : ℕ)} = ∅ := by
        ext y
        simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
          not_and]
        intro d hd
        have := d.isLt
        omega
      rw [hempty, Submodule.span_empty] at hx
      have hbot : genSub T ⊥ ≤ ⊥ :=
        sInf_le ⟨le_refl _, fun a b v hv => by rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero]⟩
      have hx0 : x = 0 := by simpa using hbot hx
      rw [hx0, map_zero]
    | succ m ih =>
      intro k hk x hx
      by_cases hkn : n ≤ k
      · exact ih k (by omega) x hx
      · replace hkn : k < n := not_le.mp hkn
        have hfil : univ.filter (fun d : Fin n => k ≤ (d : ℕ)) =
            insert ⟨k, hkn⟩ (univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ))) := by
          ext d
          simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          omega
        have hnot : (⟨k, hkn⟩ : Fin n) ∉ univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ)) := by simp
        rw [hfil, prod_insert hnot, mul_comm, map_mul, Module.End.mul_apply]
        apply ih (k + 1) (by omega)
        rw [vk_aeval_lin]
        have hmono : ∀ t : Fin n, k ≤ (t : ℕ) →
            genSub T (Submodule.span ℂ (g '' {d | t < d})) ≤
              genSub T (Submodule.span ℂ (g '' {d : Fin n | k + 1 ≤ (d : ℕ)})) := by
          intro t ht
          apply vk_genSub_mono
          apply Submodule.span_mono
          apply Set.image_mono
          intro d hd
          simp only [Set.mem_ofPred_eq, Fin.lt_def] at hd ⊢
          omega
        refine vk_genSub_map T _ (vk_shift_comm T A hAT _) _ (vk_genSub_stable T _) _ ?_ x hx
        rintro _ ⟨d, hd, rfl⟩
        simp only [Set.mem_ofPred_eq] at hd
        rcases eq_or_lt_of_le hd with h | h
        · have hdt : d = ⟨k, hkn⟩ := Fin.ext h.symm
          rw [hdt]
          exact hmono _ le_rfl (hstep _)
        · have e : (A - θ ⟨k, hkn⟩ • 1) (g d) = (A - θ d • 1) (g d) + (θ d - θ ⟨k, hkn⟩) • g d := by
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
            abel
          rw [e]
          refine add_mem (hmono d hd (hstep d)) (Submodule.smul_mem _ _ ?_)
          exact vk_le_genSub _ _ (Submodule.subset_span ⟨d, h, rfl⟩)
  intro x hx
  have h0 := main n 0 (by omega) x (by
    have : g '' {d : Fin n | 0 ≤ (d : ℕ)} = Set.range g := by
      rw [← Set.image_univ]; congr 1; ext d; simp
    rw [this]; exact hx)
  have hf : univ.filter (fun d : Fin n => 0 ≤ (d : ℕ)) = univ := by ext d; simp
  rwa [hf] at h0

theorem vk_prodShift_eq (A : Module.End ℂ W) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  rw [prodShift, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun t => ?_))
  simp [Algebra.algebraMap_eq_smul_one]

end GenKill

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section VKMain

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem vk_natCast_Ioi (c : Fin n) : (((n - 1 - (c : ℕ) : ℕ) : ℝ) : ℂ) = ((n : ℂ) - 1 - (c : ℕ)) := by
  have := c.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem vk_stepV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hdiag : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ)
    (t : Fin n) :
    (eeV E - ((thV lam t : ℝ) : ℂ) • 1) (Pi.single t φ) =
      ∑ d ∈ Ioi t, tensV E t d (Pi.single d φ) := by
  funext c
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, vk_eeV_apply, Finset.sum_apply, vk_tensV_apply, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
  rw [Pi.single_eq_same]
  rcases lt_trichotomy c t with h | h | h
  · rw [hlow t c h, Pi.single_eq_of_ne (ne_of_lt h)]
    have h1 : ∀ d ∈ Ioi t, E t d ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_lt (h.trans (mem_Ioi.1 hd))), map_zero]
    rw [Finset.sum_eq_zero h1]
    simp [ne_of_lt h]
  · subst h
    have h1 : ∀ d ∈ Ioi c, E c d ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_lt (mem_Ioi.1 hd)), map_zero]
    rw [Finset.sum_eq_zero h1, hdiag]
    simp only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Ioi, zero_add]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have := vk_natCast_Ioi c
    push_cast at this ⊢
    rw [this]
    simp only [rho, thV]
    push_cast
    ring
  · rw [Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero])
      (fun hc => absurd (mem_Ioi.2 h) hc)]
    simp [ne_of_gt h]

theorem vk_stepVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hdiag : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ)
    (s : Fin n) :
    (eeVd E - ((thVd lam s : ℝ) : ℂ) • 1) (Pi.single s φ) =
      -∑ d ∈ Iio s, tensVd E d s (Pi.single d φ) := by
  funext c
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, vk_eeVd_apply, Finset.sum_apply, vk_tensVd_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
  rw [Pi.single_eq_same]
  rcases lt_trichotomy c s with h | h | h
  · rw [Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero])
      (fun hc => absurd (mem_Iio.2 h) hc)]
    simp [ne_of_lt h]
  · subst h
    have h1 : ∀ d ∈ Iio c, E d c ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_gt (mem_Iio.1 hd)), map_zero]
    rw [Finset.sum_eq_zero h1, hdiag]
    simp only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Iio, zero_sub, neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · rw [hlow c s h, Pi.single_eq_of_ne (ne_of_gt h)]
    have h1 : ∀ d ∈ Iio s, E d s ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_gt ((mem_Iio.1 hd).trans h)), map_zero]
    rw [Finset.sum_eq_zero h1]
    simp [ne_of_gt h]

theorem vk_single_smul (c : Fin n) (r : ℂ) (x : M) :
    (Pi.single c (r • x) : Fin n → M) = r • Pi.single c x := by
  ext d
  by_cases h : d = c
  · subst h; simp
  · simp [h]

theorem vk_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (f : Fin n → M) :
    f ∈ genSub T (Submodule.span ℂ (Set.range fun t : Fin n => (Pi.single t φ : Fin n → M))) := by
  set G := genSub T (Submodule.span ℂ (Set.range fun t : Fin n => (Pi.single t φ : Fin n → M)))
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [vk_single_smul]
        exact G.smul_mem r (hx c) }
  have hφ : Submodule.span ℂ {φ} ≤ S := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    intro c
    exact vk_le_genSub T _ (Submodule.subset_span ⟨c, rfl⟩)
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (vk_genSub_stable T _ a b _ (hm c))
    simpa using h2
  have hle : genSub E (Submodule.span ℂ {φ}) ≤ S := sInf_le ⟨hφ, hSS⟩
  rw [hgen] at hle
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

theorem vk_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  rw [vk_tensV_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;> simp_all

theorem vk_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  rw [vk_tensVd_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;> simp_all

theorem vk_hT_V (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    Pi.single c (E a b m) - tensV E a b (Pi.single c m) ∈
      Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) := by
  rw [vk_tensV_single]
  split_ifs
  · have hx : (Pi.single a m : Fin n → M) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
      Submodule.subset_span ⟨a, rfl⟩
    simpa using Submodule.neg_mem _ hx
  · simp

theorem vk_hT_Vd (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    Pi.single c (E a b m) - tensVd E a b (Pi.single c m) ∈
      Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) := by
  rw [vk_tensVd_single]
  split_ifs
  · have hx : (Pi.single b m : Fin n → M) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
      Submodule.subset_span ⟨b, rfl⟩
    simpa using hx
  · simp

end VKMain

theorem verma_product_identity (n : ℕ) : VermaProductIdentity n := by
  intro M _ _ E lam φ hE hlow hdiag hgen
  constructor
  · refine LinearMap.ext fun f => ?_
    rw [vk_prodShift_eq, LinearMap.zero_apply]
    refine vk_kill (tensV E) (eeV E) (fun a b => vk_eeV_comm E hE a b) (fun t => ((thV lam t : ℝ) : ℂ))
      (fun t => (Pi.single t φ : Fin n → M)) (fun t => ?_) f (vk_gen_top E φ hgen _ (vk_hT_V E) f)
    rw [vk_stepV E lam φ hlow hdiag t]
    exact Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _
      (vk_le_genSub _ _ (Submodule.subset_span ⟨d, mem_Ioi.1 hd, rfl⟩))
  · refine LinearMap.ext fun f => ?_
    rw [vk_prodShift_eq, LinearMap.zero_apply]
    have hprod : ∏ t : Fin n, (X - C (((thVd lam t : ℝ) : ℂ))) =
        ∏ t : Fin n, (X - C (((thVd lam (Fin.rev t) : ℝ) : ℂ))) :=
      (Fintype.prod_equiv Fin.revPerm _ _ (fun t => by simp)).symm
    have hrange : Set.range (fun t : Fin n => (Pi.single (Fin.rev t) φ : Fin n → M)) =
        Set.range (fun t : Fin n => (Pi.single t φ : Fin n → M)) :=
      Fin.rev_surjective.range_comp (fun t : Fin n => (Pi.single t φ : Fin n → M))
    rw [hprod]
    refine vk_kill (tensVd E) (eeVd E) (fun a b => vk_eeVd_comm E hE a b)
      (fun t => ((thVd lam (Fin.rev t) : ℝ) : ℂ))
      (fun t => (Pi.single (Fin.rev t) φ : Fin n → M)) (fun t => ?_) f
      (by rw [hrange]; exact vk_gen_top E φ hgen _ (vk_hT_Vd E) f)
    rw [vk_stepVd E lam φ hlow hdiag (Fin.rev t)]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _
      (vk_le_genSub _ _ (Submodule.subset_span ⟨Fin.rev d, ?_, by simp⟩)))
    simp only [Set.mem_ofPred_eq]
    exact Fin.lt_rev_iff.2 (mem_Iio.1 hd)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KRel

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ X}

def IsKRel (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d → A a b * A c d - A c d * A a b =
    (if b = c then A a d else 0) - (if d = a then A c b else 0)

theorem word_isWeightVector (hA : IsKRel ε A) {ν : Fin n → ℝ} {u : X} (hu : ∀ a, A a a u = (ν a : ℂ) • u) :
    ∀ l, KirrLow ε l → ∀ a, A a a (kirrWord A u l) = (kirrWt ν l a : ℂ) • kirrWord A u l
  | [], _, a => by simpa [kirrWord, kirrWt] using hu a
  | p :: l, hl, a => by
    obtain ⟨b, c⟩ := p
    have hbc := (hl (b, c) List.mem_cons_self).2
    have ih := word_isWeightVector hA hu l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) a
    have key := LinearMap.congr_fun (hA a a b c rfl hbc) (kirrWord A u l)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
    simp only [kirrWord, kirrWt]
    rw [sub_eq_iff_eq_add, ih, map_smul] at key
    rw [key]
    by_cases h1 : a = b <;> by_cases h2 : c = a
    · subst h1; subst h2; simp [root]
    · subst h1; (simp [root, h2, Ne.symm h2, add_smul]; abel)
    · subst h2; (simp [root, h1, add_smul]; abel)
    · simp [root, h1, h2, Ne.symm h2]

theorem compact_mem_wordSpan (hA : IsKRel ε A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    ∀ l, KirrLow ε l → ∀ a b, ε a = ε b → A a b (kirrWord A u l) ∈ kirrSpan ε A u := by
  intro l
  induction l with
  | nil =>
    intro _ a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · simp [kirrWord, hu.2 a b h hab]
    · simp only [kirrWord]; rw [hu.1 a]
      exact Submodule.smul_mem _ _ (kirrWord_mem (l := []) u (by simp [KirrLow]))
    · exact kirr_low_mem h hab (kirrWord_mem (l := []) u (by simp [KirrLow]))
  | cons p l ih =>
    intro hl a b hab
    have hl' : KirrLow ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rcases lt_trichotomy a b with h | rfl | h
    · obtain ⟨x, y⟩ := p
      have hxy := hl (x, y) List.mem_cons_self
      simp only at hxy
      have key := LinearMap.congr_fun (hA a b x y hab hxy.2) (kirrWord A u l)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
      rw [sub_eq_iff_eq_add] at key
      simp only [kirrWord]
      rw [key]
      refine add_mem ?_ (kirr_low_mem hxy.1 hxy.2 (ih hl' a b hab))
      refine sub_mem ?_ ?_
      · split_ifs with h1
        · subst h1; exact ih hl' a y (hab.trans hxy.2)
        · simp
      · split_ifs with h1
        · subst h1; exact ih hl' x b (hxy.2.trans hab)
        · simp
    · rw [word_isWeightVector hA hu.1 _ hl]
      exact Submodule.smul_mem _ _ (kirrWord_mem u hl)
    · exact kirr_low_mem h hab (kirrWord_mem u hl)

theorem wordSpan_isKStable (hA : IsKRel ε A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    IsKStableSub ε A (kirrSpan ε A u) := by
  intro a b hab v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact compact_mem_wordSpan hA hu l hl a b hab
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem commute_aeval_of_commute_alt {B : Module.End ℂ X} (hB : ∀ a b, ε a = ε b → Commute (A a b) B) (u : X) :
    ∀ l, KirrLow ε l → kirrWord A (B u) l = B (kirrWord A u l)
  | [], _ => rfl
  | p :: l, hl => by
    simp only [kirrWord]
    rw [commute_aeval_of_commute_alt hB u l (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    have := (hB p.1 p.2 (hl p List.mem_cons_self).2).eq
    exact LinearMap.congr_fun this _

end KRel

section Cone

theorem root_swap_eq_neg {x y : Fin n → ℝ} (hx : InRootCone x) (hy : InRootCone y) : InRootCone (x + y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨m', rfl⟩ := hy
  refine ⟨fun a b => m a b + m' a b, ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · push_cast; rw [add_smul]
  · simp

theorem root_mem_rootCone {a b : Fin n} (h : a < b) : InRootCone (root a b) := by
  simpa using vc_inRootCone_add_root vc_inRootCone_zero' h

theorem partialSum_finset_sum (a b : Fin n) : root b a = -root a b := by
  unfold root; abel

theorem weight_sub_mem_rootCone {ε : Fin n → Bool} (ν : Fin n → ℝ) :
    ∀ l, KirrLow ε l → InRootCone (ν - kirrWt ν l)
  | [], _ => by simpa [kirrWt] using (vc_inRootCone_zero' : InRootCone (0 : Fin n → ℝ))
  | p :: l, hl => by
    have ih := weight_sub_mem_rootCone ν l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have hp := (hl p List.mem_cons_self).1
    have e : ν - kirrWt ν (p :: l) = (ν - kirrWt ν l) + root p.2 p.1 := by
      simp only [kirrWt, partialSum_finset_sum p.2 p.1]; abel
    rw [e]
    exact root_swap_eq_neg ih (root_mem_rootCone hp)

theorem wordAction_commute {ι : Type*} (t : Finset ι) (f : ι → Fin n → ℝ) (k : ℕ) :
    kirrPs k (∑ i ∈ t, f i) = ∑ i ∈ t, kirrPs k (f i) := by
  unfold kirrPs
  simp only [Finset.sum_apply]
  exact Finset.sum_comm

theorem partialSum_root_eq (k : ℕ) (x y : Fin n) :
    kirrPs k (root x y) = (if (x : ℕ) < k then 1 else 0) - (if (y : ℕ) < k then 1 else 0) := by
  unfold kirrPs root
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem partialSum_nonneg_of_rootCone {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : 0 ≤ kirrPs k β := by
  obtain ⟨m, rfl⟩ := hβ
  rw [wordAction_commute]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [wordAction_commute]
  refine Finset.sum_nonneg fun b _ => ?_
  split_ifs with h
  · have e : kirrPs k ((m a b : ℝ) • root a b) = (m a b : ℝ) * kirrPs k (root a b) := by
      simp [kirrPs, Finset.mul_sum]
    rw [e, partialSum_root_eq]
    have : (a : ℕ) < b := h
    refine mul_nonneg (by positivity) ?_
    split_ifs <;> first | omega | norm_num
  · simp [kirrPs]

theorem not_rootCone_of_ne {ε : Fin n → Bool} (ν : Fin n → ℝ) :
    ∀ l, KirrLow ε l → l ≠ [] → ¬ InRootCone (kirrWt ν l - ν)
  | [], _, h => (h rfl).elim
  | p :: l, hl, _ => by
    intro hc
    have hp := (hl p List.mem_cons_self).1
    have hle := kirrPs_wt ((p.2 : ℕ) + 1) ν l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have h1 := partialSum_nonneg_of_rootCone hc ((p.2 : ℕ) + 1)
    have e : kirrPs ((p.2 : ℕ) + 1) (kirrWt ν (p :: l) - ν) =
        kirrPs ((p.2 : ℕ) + 1) (kirrWt ν l) + kirrPs ((p.2 : ℕ) + 1) (root p.1 p.2) -
          kirrPs ((p.2 : ℕ) + 1) ν := by
      simp [kirrPs, kirrWt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [e, partialSum_root_eq] at h1
    have : (p.2 : ℕ) < p.1 := hp
    rw [if_neg (by omega), if_pos (by omega)] at h1
    linarith

end Cone

section Poly

variable {U₁ U₂ : Type*} [AddCommGroup U₁] [Module ℂ U₁] [AddCommGroup U₂] [Module ℂ U₂]

theorem rootCone_add_mem (T : U₁ →ₗ[ℂ] U₂) (A : Module.End ℂ U₁) (B : Module.End ℂ U₂)
    (h : ∀ x, T (A x) = B (T x)) (k : ℕ) : ∀ x, T ((A ^ k) x) = (B ^ k) (T x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_intertwine_alt (T : U₁ →ₗ[ℂ] U₂) (A : Module.End ℂ U₁) (B : Module.End ℂ U₂)
    (h : ∀ x, T (A x) = B (T x)) (p : ℂ[X]) (x : U₁) : T (aeval A p x) = aeval B p (T x) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, rootCone_add_mem T A B h]

theorem aeval_eigenvector {B : Module.End ℂ U₂} {c : ℂ} {y : U₂} (hy : B y = c • y) (p : ℂ[X]) :
    aeval B p y = p.eval c • y := by
  have hp : ∀ k : ℕ, (B ^ k) y = c ^ k • y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hy, smul_smul, pow_succ', mul_comm]
  rw [aeval_eq_sum_range, eval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, hp, smul_smul]

theorem lagrangeFactor_eval_ne_zero {C B : Module.End ℂ U₂} (h : Commute C B) (p : ℂ[X]) : Commute C (aeval B p) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

theorem prodShift_eq_aeval (A : Module.End ℂ U₂) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  unfold prodShift
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun t => ?_)
  simp [Algebra.algebraMap_eq_smul_one]

def k2aQ (lam : Fin n → ℝ) (s : Fin n) : ℂ[X] := ∏ t ∈ univ.erase s, (X - C ((thV lam t : ℝ) : ℂ))

theorem aux_statement_18 (lam : Fin n → ℝ) (s : Fin n) (hanti : StrictAnti lam) :
    (k2aQ lam s).eval ((thV lam s : ℝ) : ℂ) ≠ 0 := by
  unfold k2aQ
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro t ht
  simp only [eval_sub, eval_X, eval_C]
  rw [sub_ne_zero, Ne, Complex.ofReal_inj]
  unfold thV
  intro h
  have : lam s = lam t := by linarith
  exact (Finset.ne_of_mem_erase ht) (hanti.injective this).symm

theorem shifted_aeval_lagrange_eq_zero (A : Module.End ℂ U₂) (lam : Fin n → ℝ) (s : Fin n) (h0 : prodShift A (thV lam) = 0)
    (y : U₂) : (A - ((thV lam s : ℝ) : ℂ) • (1 : Module.End ℂ U₂)) (aeval A (k2aQ lam s) y) = 0 := by
  have e : (A - ((thV lam s : ℝ) : ℂ) • (1 : Module.End ℂ U₂)) * aeval A (k2aQ lam s) = prodShift A (thV lam) := by
    rw [prodShift_eq_aeval, ← Finset.mul_prod_erase univ (fun t => X - C ((thV lam t : ℝ) : ℂ)) (mem_univ s),
      map_mul]
    simp [k2aQ, Algebra.algebraMap_eq_smul_one]
  rw [← Module.End.mul_apply, e, h0, LinearMap.zero_apply]

end Poly

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
