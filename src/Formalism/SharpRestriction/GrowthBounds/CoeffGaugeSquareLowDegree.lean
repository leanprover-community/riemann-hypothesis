import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed
import Formalism.LocalToGlobal.CharacterGerms.FirstPartialLawAtPoints
import Formalism.SharpRestriction.GrowthBounds.PowerSeriesFrobeniusCongruence
import Formalism.LocalToGlobal.CharacterGerms.TripleSubstSecondCoordinate
import Formalism.LocalToGlobal.CharacterGerms.FrobPowSmul
import Formalism.LocalToGlobal.CharacterGerms.MmMulSeries
import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_tyS_Fs {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) := by
  rw [← tyS_Vpow hl]
  apply tyS_eq hl
  · intro s
    rw [map_sum]
    simp only [PowerSeries.coeff_rescale, coeff_tyS_pow hl]
    rw [← Finset.sum_mul]
    cases s with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ s =>
      have h1 : ∀ k, (ζ ^ k) ^ (l ^ (s + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  · intro m hm
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]

theorem rescale_sum_smul {ι : Type} [Fintype ι] (a : C) (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.rescale a (∑ c, u c • f c) = ∑ c, u c • PowerSeries.rescale a (f c) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem subst_pow_sum_smul {n : ℕ} (hn : 0 < n) {ι : Type} [Fintype ι] (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (∑ c, u c • f c) =
      ∑ c, u c • PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (f c) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ n) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hn.ne'])
  rw [← PowerSeries.coe_substAlgHom hS, map_sum]
  simp only [map_smul]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem coeff_one_alongCv_lg (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    PowerSeries.coeff 1 (alongCv γ (X.lg i)) = PowerSeries.coeff 1 (γ i) := by
  rw [coeff_alongCv_low le_rfl (fun j m hm => by
      have : m = 0 := by omega
      subst this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ j]) (hB.lg0 i)]
  rw [Finset.sum_eq_single i]
  · rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_neg, zero_mul]
    intro h
    exact hj (Finsupp.single_left_injective one_ne_zero h)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coeff_one_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.coeff 1 (tyS l a) = a 0 := by
  have h := coeff_tyS_pow hl a 0
  rwa [pow_zero] at h

theorem coeff_one_of_mem (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {g : Fin 2} {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {x : ℕ → I g ⊕ JJ I g → C}
    (h1 : ∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) (i : κ) :
    PowerSeries.coeff 1 (γ i) = ∑ c : I g, X.u g c i * x 0 (Sum.inl c) := by
  rw [← coeff_one_alongCv_lg X hB hγ i, h1 i, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_smul, coeff_one_tyS V.l_prime.two_le, smul_eq_mul]

end SelfConjCharts

open SelfConjCharts in
theorem r1sRestB_holds : OtherGroupCurvesClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g q
  have hl2 := V.l_prime.two_le
  set g' : Fin 2 := 1 - g with hg'
  obtain ⟨x, hx, hx0, -⟩ := (H g').t4 (X.ty g' q) (fun c => if c = q then 1 else 0)
    (fun c => by split_ifs <;> simp [VF.Ge.zero, VF.Ge.one])
    (fun c hc => by
      rw [if_neg]
      rintro rfl
      exact hc rfl)
  have hF := (H g').Fm x hx
  obtain ⟨z, -, hz, -, hz1, -⟩ := id hx
  obtain ⟨ε, -, hε, -, hε1, -⟩ := hF
  refine ⟨z, ε, fun q' => Fs V.l x 0 (Sum.inl q'), hz, hε, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hε1 i, hz1 i, subst_pow_sum_smul (by omega)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    exact subst_tyS_Fs hl2 hζ (fun s => x s (Sum.inl c))
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hz i).1) hz1 i, hx0]
    simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hε i).1) hε1 i]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · intro q'
    exact (H g').t2 _ ((H g').Fm x hx) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_X_pow_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) f := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  rw [PowerSeries.subst_comp_subst_apply hS hS]
  congr 1
  rw [← PowerSeries.coe_substAlgHom hS, map_pow, PowerSeries.coe_substAlgHom hS, PowerSeries.subst_X hS, ← pow_mul, sq]

theorem sum_rescale_tyS_two {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) (ha : a 1 = 0) :
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (tyS l fun s => (l : C) * a (s + 2)) := by
  have e : (fun s => (l : C) * a (s + 1)) = fun s => if s < 1 then 0 else (l : C) * a (s - 1 + 2) := by
    funext s
    cases s with
    | zero => simp [ha]
    | succ s => simp
  rw [← subst_tyS_Fs hl hζ a, ← subst_X_pow_X_pow (by omega)]
  congr 1
  rw [← tyS_Vpow hl, e]

theorem sum_root_pow {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range l, (ζ ^ k) ^ (l ^ j) = (l : C) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : ∀ k, (ζ ^ k) ^ (l ^ (i + 1)) = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
  simp [h1]

theorem coeff_sum_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) (f : PowerSeries C) :
    PowerSeries.coeff (l ^ j) (∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) f) =
      (l : C) * PowerSeries.coeff (l ^ j) f := by
  rw [map_sum]
  simp only [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_root_pow hζ j hj]

section MM

variable {V : VF C}

theorem mmA_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mmA_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mmA_sum {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mmA_add) mmA_zero h

theorem mmA_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' hb ha

end MM

end SelfConjCharts

open SelfConjCharts in
theorem good_curve_closed : GoodCurveClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g a w x hG hV2
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hxT : x ∈ X.TySet V g := hG.1.1
  have hx1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2

  have hyT : Vpow 1 (fun i n => (V.l : C) * x (i + 2) n) ∈ X.TySet V g := by
    have hF := (H g).Fm x hxT
    have h3 := (H g).t3 (fun q => (RawChart.cart (H g)).c0' x q) (fun q => hG.c0'_int q)
    have hsub := (H g).add _ _ hF ((H g).neg _ h3)
    convert hsub using 1
    funext i n
    cases i with
    | zero =>
      cases n with
      | inl c => simp [Vpow, Fs, const0, hx1 c]
      | inr q => simp [Vpow, Fs, const0, Cart.c0']
    | succ i => simp [Vpow, Fs, const0]
  have hyT' := X.unV_mem V g hB.lg0 hB.exlg hζ _ hyT
  obtain ⟨γ, lam, hγ, hlam, hγ1, hγ2⟩ := id hxT
  obtain ⟨δ, -, hδ, -, hδ1, -⟩ := hyT'
  refine ⟨γ, δ, hγ, hδ, ?_, ?_, ?_⟩
  ·
    intro i
    rw [hδ1 i, hγ1 i, subst_pow_sum_smul (by positivity)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum, sum_rescale_tyS_two hl2 hζ _ (hx1 c)]
  · intro i
    rw [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1 i]
    exact mmA_sum _ _ fun c _ => MaximalIdealCongruence.mm_mul_ge' (hB.uint g c i) (hV2 c)
  · intro q
    have hA : ∀ n, PowerSeries.coeff n (alongCv γ (X.sg (X.u (1 - g) q))) =
        PowerSeries.coeff n (lam q) - PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inr q)) +
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inl c)) else 0) := by
      intro n
      have e := congrArg (PowerSeries.coeff n) (hγ2 q)
      simp only [map_add, map_sub, map_sum, apply_ite (PowerSeries.coeff n), PowerSeries.coeff_smul, map_zero,
        smul_eq_mul] at e
      linear_combination e
    have hT1 : ∀ b : ℕ → C, PowerSeries.coeff V.l (tyS V.l b) = b 1 := fun b => by
      simpa using coeff_tyS_pow hl2 b 1
    have hT2 : ∀ b : ℕ → C, PowerSeries.coeff (V.l ^ 2) (tyS V.l b) = b 2 := fun b => coeff_tyS_pow hl2 b 2
    have hN1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
        (V.l : C) * PowerSeries.coeff V.l f := fun f => by simpa using coeff_sum_rescale hζ 1 le_rfl f
    have hN2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
          (V.l : C) * PowerSeries.coeff (V.l ^ 2) f := fun f => coeff_sum_rescale hζ 2 (by norm_num) f
    have hl2pos : 0 < V.l ^ 2 := by positivity
    have hS1 : ∀ f : PowerSeries C,
        PowerSeries.coeff V.l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = 0 := fun f =>
      coeff_subst_X_pow_of_not_dvd hl2pos f V.l (fun h => by
        have := Nat.le_of_dvd hl0 h
        nlinarith)
    have hS2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) =
          PowerSeries.coeff 1 f := fun f => by simpa using coeff_subst_X_pow hl2pos f 1
    refine ⟨hG.c0'_int q, ?_, ?_⟩
    · have e : PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q =
          -((V.l : C) * PowerSeries.coeff V.l (lam q)) := by
        unfold phi
        rw [map_sub, hS1, hN1, hA]
        simp only [hT1, hx1, mul_zero, ite_self, Finset.sum_const_zero, add_zero, Cart.c0']
        ring
      rw [e]
      exact MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _))
    · have hB1 : PowerSeries.coeff 1 (alongCv δ (X.sg (X.u (1 - g) q))) =
          ∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q) := by
        rw [coeff_alongCv_low le_rfl (fun j m hm => by
            obtain rfl : m = 0 := by omega
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ j).1]) (X.constantCoeff_sg hB.axis0 _)]
        simp only [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1,
          RawChart.sg1, Finset.mul_sum, zero_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have key : (∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) -
          (V.l : C) * ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * x 2 (Sum.inl c) else 0) =
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> ring
      have e : PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q) =
          (∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q))) +
            -((V.l : C) * PowerSeries.coeff (V.l ^ 2) (lam q)) := by
        unfold phi
        rw [map_sub, hS2, hN2, hA, hB1]
        simp only [hT2]
        linear_combination key
      rw [e]
      refine mmA_add (mmA_sum _ _ fun c _ => ?_) (MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)))
      split_ifs with hm
      · exact mmA_zero
      · exact mmA_mul_int (hV2 c) (hB.hmis g c q hm)

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace SelfConjDifferentials

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constantCoeff_unshift_logarithm (Y : FBChart C V O dd) (i : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0 := by
  rw [constantCoeff_uncurry, Y.lg_const]

theorem sum_range_list {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem exp_sum_range {σ : Type} (f : ℕ → MvPowerSeries σ C) (hf : ∀ k, MvPowerSeries.constantCoeff (f k) = 0)
    (n : ℕ) : mvExp (∑ k ∈ Finset.range n, f k) = ((List.range n).map fun k => mvExp (f k)).prod := by
  induction n with
  | zero => simp [rtj_mvExp_zero]
  | succ n ih =>
    have h0 : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, f k) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => hf k
    rw [Finset.sum_range_succ, VP.exp_add h0 (hf n), ih, List.range_succ, List.map_append, List.prod_append]
    simp

theorem lg_zero (Y : FBChart C V O dd) {τ : Type} (i : Fin dd) :
    MvPowerSeries.subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) (un1 (Y.lg i)) = 0 := by
  show MvPowerSeries.subst (0 : Fin dd → MvPowerSeries τ C) (un1 (Y.lg i)) = 0
  rw [MvPowerSeries.subst_zero_eq_C_constantCoeff, constantCoeff_unshift_logarithm]
  simp

theorem subst_add_logarithm_additive (Y : FBChart C V O dd) {τ : Type} (a b : Fin dd → MvPowerSeries τ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0)
    (i : Fin dd) :
    MvPowerSeries.subst (VP.addAt Y a b) (un1 (Y.lg i)) =
      MvPowerSeries.subst a (un1 (Y.lg i)) + MvPowerSeries.subst b (un1 (Y.lg i)) := by
  have h := lg_addOf Y ![a, b] (fun k j => by fin_cases k; exacts [ha j, hb j]) i
  have e : (fun q : Fin 2 × Fin dd => (![a, b] : Fin 2 → Fin dd → MvPowerSeries τ C) q.1 q.2) = VP.P2 a b := by
    funext q
    obtain ⟨k, j⟩ := q
    fin_cases k <;> simp [VP.P2]
  rw [e] at h
  exact h

theorem lg_sumL (Y : FBChart C V O dd) {τ : Type} (i : Fin dd) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, VP.GoodPt V a) →
      MvPowerSeries.subst (VP.sumL Y l) (un1 (Y.lg i)) = (l.map fun a => MvPowerSeries.subst a (un1 (Y.lg i))).sum
  | [], _ => by
    show MvPowerSeries.subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) (un1 (Y.lg i)) = _
    rw [lg_zero, List.map_nil, List.sum_nil]
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    have hl : ∀ b ∈ l, VP.GoodPt V b := fun b hb => h b (List.mem_cons_of_mem _ hb)
    show MvPowerSeries.subst (VP.addAt Y a (VP.sumL Y l)) (un1 (Y.lg i)) = _
    rw [subst_add_logarithm_additive Y a _ ha.1 (VP.good_sumL Y l hl).1, lg_sumL Y i l hl, List.map_cons, List.sum_cons]

theorem pt_eq_of_lg (Y : FBChart C V O dd) {τ : Type} {A B : Fin dd → MvPowerSeries τ C}
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (hB : ∀ j, MvPowerSeries.constantCoeff (B j) = 0)
    (h : ∀ i, MvPowerSeries.subst A (un1 (Y.lg i)) = MvPowerSeries.subst B (un1 (Y.lg i))) : A = B := by
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => constantCoeff_unshift_logarithm Y j
  have key : ∀ A : Fin dd → MvPowerSeries τ C, (∀ j, MvPowerSeries.constantCoeff (A j) = 0) → ∀ i,
      MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
    intro A hA i
    have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
    have hx : un1 (comp1 Y.ex Y.lg i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
      rw [Y.ex_lg]; exact uncurry_X i
    rw [← MvPowerSeries.subst_comp_subst_apply hL hA', uncurry_comp Y.lg_const, hx, MvPowerSeries.subst_X hA']
  funext i
  rw [← key A hA i, ← key B hB i]
  simp only [h]

theorem hAt_self (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) {τ : Type}
    (a b : Fin 2 × Fin dd → MvPowerSeries τ C) (ha : ∀ x, MvPowerSeries.constantCoeff (a x) = 0)
    (hb : ∀ x, MvPowerSeries.constantCoeff (b x) = 0) :
    SelfConjCharts.hAt (Y.rawSelf p) a b = ∑ col : Fin 2, VP.hAt Y (fun x => a (col, x)) (fun x => b (col, x)) := by
  have hP : MvPowerSeries.HasSubst (SelfConjCharts.pairSubst a b) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      unfold SelfConjCharts.pairSubst
      split_ifs
      exacts [ha _, hb _]
  have hc : ∀ col : Fin 2, MvPowerSeries.subst (SelfConjCharts.pairSubst a b) (hCol col Y.h) =
      VP.hAt Y (fun x => a (col, x)) (fun x => b (col, x)) := by
    intro col
    have hI : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
        (MvPowerSeries.X (q.1, (col, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
    unfold hCol
    rw [MvPowerSeries.subst_comp_subst_apply hI hP]
    show _ = MvPowerSeries.subst (VP.P2 _ _) Y.h
    congr 1
    funext q
    rw [MvPowerSeries.subst_X hP]
    rfl
  show MvPowerSeries.subst (SelfConjCharts.pairSubst a b) (∑ col, hCol col Y.h) = _
  rw [Fin.sum_univ_two, Fin.sum_univ_two, MvPowerSeries.subst_add hP, hc 0, hc 1]

theorem col_left (Y : FBChart C V O dd) {τ : Type} (n : ℕ) (a : ℕ → Fin dd → MvPowerSeries τ C)
    {s c : Fin dd → MvPowerSeries τ C} (ha : ∀ k, VP.GoodPt V (a k)) (hs : VP.GoodPt V s) (hc : VP.GoodPt V c)
    (hsum : s = VP.sumL Y ((List.range n).map a)) :
    IntS V (mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c)) ∧
      MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c) = 0 := by
  obtain ⟨U, hU, e⟩ := VP.biadd_left Y hc ((List.range n).map a) (by
    intro b hb
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
    exact ha k)
  rw [← hsum, List.map_map] at e
  have c1 : ∀ k, MvPowerSeries.constantCoeff (VP.hAt Y (a k) c) = 0 := fun k => VP.cc_hAt Y (ha k).1 hc.1
  have c2 : MvPowerSeries.constantCoeff (VP.hAt Y s c) = 0 := VP.cc_hAt Y hs.1 hc.1
  have cS : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y (a k) c) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => c1 k
  have c2' : MvPowerSeries.constantCoeff (-VP.hAt Y s c) = 0 := by rw [map_neg, c2, neg_zero]
  have hU' : mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c) = mvExp (VP.hAt Y s c) * U := by
    rw [exp_sum_range (fun k => VP.hAt Y (a k) c) c1 n, e]
    rfl
  have inv : mvExp (VP.hAt Y s c) * mvExp (-VP.hAt Y s c) = 1 := by
    rw [← VP.exp_add c2 c2', add_neg_cancel, rtj_mvExp_zero]
  have key : mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c) = U := by
    rw [sub_eq_add_neg, VP.exp_add cS c2', hU', mul_comm (mvExp (VP.hAt Y s c)) U, mul_assoc, inv, mul_one]
  refine ⟨?_, by rw [map_sub, cS, c2, sub_zero]⟩
  rw [key]
  exact hU.1

theorem col_right (Y : FBChart C V O dd) {τ : Type} (n : ℕ) (a : ℕ → Fin dd → MvPowerSeries τ C)
    {s c : Fin dd → MvPowerSeries τ C} (ha : ∀ k, VP.GoodPt V (a k)) (hs : VP.GoodPt V s) (hc : VP.GoodPt V c)
    (hsum : s = VP.sumL Y ((List.range n).map a)) :
    IntS V (mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s)) ∧
      MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s) = 0 := by
  obtain ⟨U, hU, e⟩ := VP.biadd_right Y hc ((List.range n).map a) (by
    intro b hb
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
    exact ha k)
  rw [← hsum, List.map_map] at e
  have c1 : ∀ k, MvPowerSeries.constantCoeff (VP.hAt Y c (a k)) = 0 := fun k => VP.cc_hAt Y hc.1 (ha k).1
  have c2 : MvPowerSeries.constantCoeff (VP.hAt Y c s) = 0 := VP.cc_hAt Y hc.1 hs.1
  have cS : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y c (a k)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => c1 k
  have c2' : MvPowerSeries.constantCoeff (-VP.hAt Y c s) = 0 := by rw [map_neg, c2, neg_zero]
  have hU' : mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k)) = mvExp (VP.hAt Y c s) * U := by
    rw [exp_sum_range (fun k => VP.hAt Y c (a k)) c1 n, e]
    rfl
  have inv : mvExp (VP.hAt Y c s) * mvExp (-VP.hAt Y c s) = 1 := by
    rw [← VP.exp_add c2 c2', add_neg_cancel, rtj_mvExp_zero]
  have key : mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s) = U := by
    rw [sub_eq_add_neg, VP.exp_add cS c2', hU', mul_comm (mvExp (VP.hAt Y c s)) U, mul_assoc, inv, mul_one]
  refine ⟨?_, by rw [map_sub, cS, c2, sub_zero]⟩
  rw [key]
  exact hU.1

theorem biInt_self (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    SelfConjCharts.BiInt (Y.rawSelf p) V := by
  intro τ _ n a s c ha hs hc hlg
  have gp : ∀ {b : Fin 2 × Fin dd → MvPowerSeries τ C}, SelfConjCharts.IsPt V b → ∀ col : Fin 2,
      VP.GoodPt V (fun x => b (col, x)) :=
    fun hb col => ⟨fun x => (hb (col, x)).1, fun x => (hb (col, x)).2⟩
  have cc0 : ∀ {b : Fin 2 × Fin dd → MvPowerSeries τ C}, SelfConjCharts.IsPt V b → ∀ q,
      MvPowerSeries.constantCoeff (b q) = 0 :=
    fun hb q => (hb q).1
  have hsum : ∀ col : Fin 2,
      (fun x => s (col, x)) = VP.sumL Y ((List.range n).map fun k x => a k (col, x)) := by
    intro col
    have hl : ∀ b ∈ (List.range n).map (fun k x => a k (col, x)), VP.GoodPt V b := by
      intro b hb
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
      exact gp (ha k) col
    apply pt_eq_of_lg Y (gp hs col).1 (VP.good_sumL Y _ hl).1
    intro i
    rw [lg_sumL Y i _ hl, List.map_map]
    have h := hlg (col, i)
    change MvPowerSeries.subst s (inCol col (un1 (Y.lg i))) =
      ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (inCol col (un1 (Y.lg i))) at h
    have h2 : ∀ k, MvPowerSeries.subst (a k) (inCol col (un1 (Y.lg i))) =
        MvPowerSeries.subst (fun x => a k (col, x)) (un1 (Y.lg i)) :=
      fun k => subst_inCol (cc0 (ha k)) col _
    rw [subst_inCol (cc0 hs)] at h
    simp only [h2] at h
    rw [h, sum_range_list]
    rfl
  constructor
  · have e : ∑ k ∈ Finset.range n, SelfConjCharts.hAt (Y.rawSelf p) (a k) c - SelfConjCharts.hAt (Y.rawSelf p) s c =
        ∑ col : Fin 2, (∑ k ∈ Finset.range n, VP.hAt Y (fun x => a k (col, x)) (fun x => c (col, x)) -
          VP.hAt Y (fun x => s (col, x)) (fun x => c (col, x))) := by
      rw [Finset.sum_congr rfl fun k _ => hAt_self Y p (a k) c (cc0 (ha k)) (cc0 hc),
        hAt_self Y p s c (cc0 hs) (cc0 hc), Finset.sum_comm, ← Finset.sum_sub_distrib]
    have h0 := col_left Y n (fun k x => a k (0, x)) (fun k => gp (ha k) 0) (gp hs 0) (gp hc 0) (hsum 0)
    have h1 := col_left Y n (fun k x => a k (1, x)) (fun k => gp (ha k) 1) (gp hs 1) (gp hc 1) (hsum 1)
    rw [e, Fin.sum_univ_two, VP.exp_add h0.2 h1.2]
    exact h0.1.mul h1.1
  · have e : ∑ k ∈ Finset.range n, SelfConjCharts.hAt (Y.rawSelf p) c (a k) - SelfConjCharts.hAt (Y.rawSelf p) c s =
        ∑ col : Fin 2, (∑ k ∈ Finset.range n, VP.hAt Y (fun x => c (col, x)) (fun x => a k (col, x)) -
          VP.hAt Y (fun x => c (col, x)) (fun x => s (col, x))) := by
      rw [Finset.sum_congr rfl fun k _ => hAt_self Y p c (a k) (cc0 hc) (cc0 (ha k)),
        hAt_self Y p c s (cc0 hc) (cc0 hs), Finset.sum_comm, ← Finset.sum_sub_distrib]
    have h0 := col_right Y n (fun k x => a k (0, x)) (fun k => gp (ha k) 0) (gp hs 0) (gp hc 0) (hsum 0)
    have h1 := col_right Y n (fun k x => a k (1, x)) (fun k => gp (ha k) 1) (gp hs 1) (gp hc 1) (hsum 1)
    rw [e, Fin.sum_univ_two, VP.exp_add h0.2 h1.2]
    exact h0.1.mul h1.1

end SelfConjDifferentials

theorem biadditive_on_columns : BiadditiveOnColumns := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  exact SelfConjDifferentials.biInt_self Y p

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MaximalIdealCongruence

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem sg_lin (X : RawChart C d I κ) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    X.sg (fun i => ∑ q, m q * u q i) = ∑ q, m q • X.sg (u q) := by
  apply MvPowerSeries.ext
  intro μ
  rw [map_sum]
  simp only [MvPowerSeries.coeff_smul]
  show -∑ i, (∑ q, m q * u q i) * _ = ∑ q, m q * -∑ i, u q i * _
  simp only [Finset.sum_mul, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem alongCv_lin {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {ι : Type} [Fintype ι]
    (m : ι → C) (f : ι → MvPowerSeries κ C) : alongCv γ (∑ q, m q • f q) = ∑ q, m q • alongCv γ (f q) := by
  have hS : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  unfold alongCv
  simp only [← MvPowerSeries.substAlgHom_apply hS, map_sum, map_smul]

theorem phi_lin (X : RawChart C d I κ) (l : ℕ) (hl : 0 < l) (ζ : C) {γ δ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    phi X l ζ γ δ (fun i => ∑ q, m q * u q i) = ∑ q, m q • phi X l ζ γ δ (u q) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  unfold phi
  rw [sg_lin, alongCv_lin hγ, alongCv_lin hδ]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
  congr 1
  · simp only [← PowerSeries.coe_substAlgHom hS, map_sum, map_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
    ring

theorem ge_of_mm {V : VF C} {a : C} (h : V.MM a) : V.Ge 0 a := by
  unfold VF.MM at h
  unfold VF.Ge
  exact_mod_cast le_of_lt h

theorem mm_pow_sub {V : VF C} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.MM (a - b)) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by
  rw [← geom_sum₂_mul]
  exact mm_mul_ge' (VF.Ge.sum fun i _ => by simpa using (ha.pow i).mul (hb.pow (n - 1 - i))) h

theorem coeffIdentity_plainChart_of_three [IsAlgClosed C] [CharZero C] (X : RawChart C d I κ) (V : VF C) (H : ∀ g, X.CartHyp V g)
    (hA : StepA X V H) (hB : StepB X V) (hC : LemC X V) : IndependenceBoundPlain.PlainCoefficientIdentity X H := by
  intro _ g a _
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have hl0 : 0 < V.l := V.l_prime.pos
  choose z ε m hz hε hrel hz1 hε1 hm using hB ζ hζ g
  refine ⟨fun q' q => m q q', fun w x hg hV => ?_⟩
  obtain ⟨γ, δ, hγ, hδ, hrel', hmm, hq⟩ := hA ζ hζ g a w x hg hV
  refine ⟨fun q' => (V.l : C) * x 2 (Sum.inr q'), fun q hne => ?_, fun q => ?_⟩
  · have h2 := hg.1.2.2 2 (Sum.inr q) (by
      show X.ty (1 - g) q ≠ a + ((2 : ℕ) : ZMod d)
      simpa using hne)
    show (V.l : C) * x 2 (Sum.inr q) = 0
    rw [h2, mul_zero]
  · have h1 := hC ζ hζ γ δ (z q) (ε q) hγ hδ (hz q) (hε q) hrel' (hrel q) hmm
    rw [funext (hz1 q), funext (hε1 q), phi_lin X V.l hl0 ζ (fun i => (hγ i).1) (fun i => (hδ i).1), map_sum] at h1
    simp only [PowerSeries.coeff_smul, smul_eq_mul] at h1
    obtain ⟨hc0, hcA, _⟩ := hq q
    have hAint : V.Ge 0 (PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q))) := by
      have := (ge_of_mm hcA).add hc0
      simpa using this
    have h3 := mm_pow_sub hAint hc0 hcA V.l
    have h4 : V.MM (∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
        (V.l : C) * x 2 (Sum.inr q'))) := mm_sum _ _ fun q' _ => mm_mul_ge' (hm q q') (hq q').2.2
    have e : (RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' =
        -(PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l - (RawChart.cart (H g)).c0' x q ^ V.l) +
        ((PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l -
          ∑ q', m q q' * PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q'))) +
        ∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
          (V.l : C) * x 2 (Sum.inr q'))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have : ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' = ∑ q', m q q' * ((V.l : C) * x 2 (Sum.inr q')) :=
        Finset.sum_congr rfl fun q' _ => by ring
      rw [this]
      ring
    rw [e]
    exact mm_add (mm_neg h3) (mm_add h1 h4)

end SelfConjCharts

section Self

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

theorem FBChart.rawSelf_axis1 (Y : FBChart C V O dd) (p : SelfData Y d I0) (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ)
    (he : ∀ s ∈ e.support, s.1 ≠ 1) : MvPowerSeries.coeff e (Y.rawSelf p).h = 0 := by
  show MvPowerSeries.coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 1 Y.h (gauge_axes Y 1)) e he

theorem FBChart.rawSelf_basic (Y : FBChart C V O dd) (p : SelfData Y d I0) : SelfConjCharts.Basic (Y.rawSelf p) V where
  lg0 := Y.self_chart_log_constantCoeff p
  exlg := Y.rawSelf_exlg p
  lin := Y.rawSelf_lin p
  axis0 := Y.rawSelf_axis0 p
  axis1 := Y.rawSelf_axis1 p
  uint := Y.rawSelf_u_integral p
  hmis := hStabSelf_holds C V O dd Y d I0 p

end Self

theorem coeffIdentity_selfConj_of_four (hA : GoodCurveClosed) (hB : OtherGroupCurvesClosed) (hC : MixedCoefficientClosed) (hD : BiadditiveOnColumns) : CoefficientIdentitySelfConjugate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p _ H
  have := Y.algClosed
  have hb := Y.rawSelf_basic p
  exact SelfConjCharts.coeffIdentity_plainChart_of_three (Y.rawSelf p) V H (hA C V d _ _ _ hb H) (hB C V d _ _ _ hb H)
    (hC C V d _ _ _ hb (hD C V O dd Y d I0 p))

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MaximalIdealCongruence MvPowerSeries

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem ee_zero (i j : ℕ) : ee i j 0 = i := by simp [ee]

theorem ee_one (i j : ℕ) : ee i j 1 = j := by simp [ee]

theorem eq_ee (μ : Fin 2 →₀ ℕ) : μ = ee (μ 0) (μ 1) := by
  ext x
  fin_cases x <;> simp [ee]

theorem ee_00 : ee 0 0 = 0 := by simp [ee]

theorem ee_ne {i j : ℕ} (h : j ≠ 0) : ee i j ≠ 0 := fun e => h (by
  have := DFunLike.congr_fun e 1
  simpa [ee_one] using this)

theorem smul_ee (l i j : ℕ) : l • ee i j = ee (l * i) (l * j) := by
  simp [ee, smul_add, Finsupp.smul_single]

theorem kmul {f g : MvPowerSeries (Fin 2) C} {a b : ℕ} (hf : ∀ i j, j < a → coeff (ee i j) f = 0)
    (hg : ∀ i j, j < b → coeff (ee i j) g = 0) (i j : ℕ) (h : j < a + b) : coeff (ee i j) (f * g) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have e1 : p 1 + q 1 = j := by
    have := DFunLike.congr_fun e 1
    simpa [ee_one] using this
  show coeff p f * coeff q g = 0
  by_cases hp : p 1 < a
  · have : coeff p f = 0 := by rw [eq_ee p]; exact hf _ _ hp
    rw [this, zero_mul]
  · have : coeff q g = 0 := by rw [eq_ee q]; exact hg _ _ (by omega)
    rw [this, mul_zero]

theorem jmul {V : VF C} {f g : MvPowerSeries (Fin 2) C} {N : ℕ} (hf : ∀ i j, i ≤ N → V.MM (coeff (ee i j) f))
    (hg : IntS V g) (i j : ℕ) (h : i ≤ N) : V.MM (coeff (ee i j) (f * g)) := by
  rw [MvPowerSeries.coeff_mul]
  refine mm_sum _ _ ?_
  rintro ⟨p, q⟩ hpq
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have e1 : p 0 + q 0 = i := by
    have := DFunLike.congr_fun e 0
    simpa [ee_zero] using this
  show V.MM (coeff p f * coeff q g)
  have : V.MM (coeff p f) := by rw [eq_ee p]; exact hf _ _ (by omega)
  exact mm_mul_ge this (hg q)

theorem mvExp_rs (j : Fin 2) (c : C) (F : MvPowerSeries (Fin 2) C) : mvExp (rs j c F) = rs j c (mvExp F) := by
  apply MvPowerSeries.ext
  intro m
  unfold rs
  rw [MvPowerSeries.coeff_rescale]
  show ∑ k ∈ Finset.range (m.degree + 1), coeff m ((MvPowerSeries.rescale _ F) ^ k) / (k.factorial : C) =
    _ * ∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, MvPowerSeries.coeff_rescale, mul_div_assoc]

theorem alongCv_rc {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (c : C)
    (f : MvPowerSeries κ C) : alongCv (rc c γ) f = PowerSeries.rescale c (alongCv γ f) := by
  unfold rc
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f

theorem alongCv_pw {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {n : ℕ} (hn : 0 < n)
    (f : MvPowerSeries κ C) :
    alongCv (pw n γ) f = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv γ f) := by
  unfold pw
  exact alongCv_repar hγ (by simp [hn.ne']) f

theorem rc_cc {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (c : C) (i : κ) :
    PowerSeries.constantCoeff (rc c γ i) = 0 := by
  unfold rc
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ i, mul_zero]

theorem pw_low {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {n : ℕ} (hn : 0 < n) (i : κ)
    (j : ℕ) (hj : j < n) : PowerSeries.coeff j (pw n γ i) = 0 := by
  unfold pw
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have := coeff_subst_X_pow hn (γ i) 0
    rw [mul_zero] at this
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ i]
  · exact coeff_subst_X_pow_of_not_dvd hn _ j (Nat.not_dvd_of_pos_of_lt hj0 hj)

theorem pw_lead (γ : κ → PowerSeries C) {n : ℕ} (hn : 0 < n) (i : κ) :
    PowerSeries.coeff n (pw n γ i) = PowerSeries.coeff 1 (γ i) := by
  unfold pw
  have := coeff_subst_X_pow hn (γ i) 1
  rwa [mul_one] at this

theorem sg_smul (X : RawChart C d I κ) (c : C) (v : κ → C) : X.sg (fun i => c * v i) = c • X.sg v := by
  simpa using sg_lin X (fun _ : Unit => c) (fun _ => v)

theorem alongCv_smul {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (c : C)
    (f : MvPowerSeries κ C) : alongCv γ (c • f) = c • alongCv γ f := by
  simpa using alongCv_lin hγ (fun _ : Unit => c) (fun _ => f)

end SelfConjCharts

open SelfConjCharts MaximalIdealCongruence MvPowerSeries

theorem r1sRestC_of (hFr : PowerSeriesFrobeniusCongruence) (hRo : RootsOfUnityProductCongruence) (hEx : ExpLowOrderTruncation) (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry)
    (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : MixedCoefficientClosed := by
  intro C _ _ V d I _ κ _ X hb hBi ζ hζ γ δ z ε hγ hδ hz hε hrel hrel' hmm
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hll : 0 < V.l ^ 2 := by positivity
  have hζ1 := hζ.pow_eq_one
  have cγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have cδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0 := fun i => (hδ i).1
  have cz : ∀ i, PowerSeries.constantCoeff (z i) = 0 := fun i => (hz i).1
  have cε : ∀ i, PowerSeries.constantCoeff (ε i) = 0 := fun i => (hε i).1
  have low1 : ∀ c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (c i) = 0) →
      ∀ i j, j < 1 → PowerSeries.coeff j (c i) = 0 := by
    intro c hc i j hj
    obtain rfl : j = 0 := by omega
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hc i]
  have cX : ∀ i, PowerSeries.constantCoeff (pw (V.l ^ 2) δ i) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact pw_low cδ hll i 0 hll
  have cZ : ∀ i, PowerSeries.constantCoeff (pw V.l ε i) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact pw_low cε hl0 i 0 hl0
  have HL := hHL C d I κ X hb.axis1
  set aC : (κ → PowerSeries C) → MvPowerSeries (Fin 2) C := fun c =>
    ∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw (V.l ^ 2) δ) c with haC
  set bC : (κ → PowerSeries C) → MvPowerSeries (Fin 2) C := fun c =>
    ∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) z) - HH X c (pw V.l ε) with hbC

  have aK : ∀ (c : κ → PowerSeries C) (m : ℕ), 1 ≤ m → (∀ i j, j < m → PowerSeries.coeff j (c i) = 0) →
      (∀ n j, j < m → coeff (ee n j) (aC c) = 0) ∧
        ∀ n, coeff (ee n m) (aC c) = PowerSeries.coeff n (phi X V.l ζ γ δ fun i => PowerSeries.coeff m (c i)) := by
    intro c m hm hc
    constructor
    · intro n j hj
      simp only [haC, map_sub, map_sum]
      rw [(HL _ c cX m hm hc).1 n j hj, Finset.sum_eq_zero fun k _ => (HL _ c (rc_cc cγ _) m hm hc).1 n j hj, sub_zero]
    · intro n
      simp only [haC, map_sub, map_sum]
      rw [(HL _ c cX m hm hc).2 n, Finset.sum_congr rfl fun k _ => (HL _ c (rc_cc cγ (ζ ^ k)) m hm hc).2 n]
      unfold phi
      simp only [map_sub, map_sum, alongCv_rc cγ, alongCv_pw cδ hll, Finset.sum_neg_distrib]
      ring

  have bK : ∀ x : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (x i) = 0) →
      (∀ n, coeff (ee n 0) (bC x) = 0) ∧ ∀ n, coeff (ee n 1) (bC x) = 0 := by
    intro x hx
    constructor
    · intro n
      simp only [hbC, map_sub, map_sum]
      rw [(HL x _ hx 1 le_rfl (low1 _ cZ)).1 n 0 one_pos,
        Finset.sum_eq_zero fun k _ => (HL x _ hx 1 le_rfl (low1 _ (rc_cc cz (ζ ^ k)))).1 n 0 one_pos, sub_zero]
    · intro n
      simp only [hbC, map_sub, map_sum]
      rw [(HL x _ hx V.l hl0 (pw_low cε hl0)).1 n 1 (by omega),
        Finset.sum_congr rfl fun k _ => (HL x _ hx 1 le_rfl (low1 _ (rc_cc cz (ζ ^ k)))).2 n, sub_zero]
      have e : ∀ k, (fun i => PowerSeries.coeff 1 (rc (ζ ^ k) z i)) = fun i => ζ ^ k * PowerSeries.coeff 1 (z i) := by
        intro k
        funext i
        unfold rc
        rw [PowerSeries.coeff_rescale, pow_one]
      simp only [e, sg_smul, alongCv_smul hx, PowerSeries.coeff_smul, smul_eq_mul]
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hζ.geom_sum_eq_zero (by omega), zero_mul, neg_zero]
  have ccOf : ∀ F : MvPowerSeries (Fin 2) C, coeff (ee 0 0) F = 0 → constantCoeff F = 0 := by
    intro F h
    rwa [ee_00, coeff_zero_eq_constantCoeff_apply] at h
  have cca : ∀ c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (c i) = 0) → constantCoeff (aC c) = 0 :=
    fun c hc => ccOf _ ((aK c 1 le_rfl (low1 c hc)).1 0 0 one_pos)
  have ccb : ∀ c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (c i) = 0) → constantCoeff (bC c) = 0 :=
    fun c hc => ccOf _ ((bK c hc).1 0)

  have hid : bC (pw (V.l ^ 2) δ) + ∑ k ∈ Finset.range V.l, aC (rc (ζ ^ k) z) =
      aC (pw V.l ε) + ∑ k ∈ Finset.range V.l, bC (rc (ζ ^ k) γ) := by
    simp only [haC, hbC, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    ring
  have hE : mvExp (bC (pw (V.l ^ 2) δ)) * ∏ k ∈ Finset.range V.l, mvExp (aC (rc (ζ ^ k) z)) =
      mvExp (aC (pw V.l ε)) * ∏ k ∈ Finset.range V.l, mvExp (bC (rc (ζ ^ k) γ)) := by
    rw [← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun k _ => cca _ (rc_cc cz _)),
      ← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun k _ => ccb _ (rc_cc cγ _)),
      ← VP.exp_add (ccb _ cX) (by rw [map_sum]; exact Finset.sum_eq_zero fun k _ => cca _ (rc_cc cz _)),
      ← VP.exp_add (cca _ cZ) (by rw [map_sum]; exact Finset.sum_eq_zero fun k _ => ccb _ (rc_cc cγ _)), hid]
  have ars : ∀ c : C, aC (rc c z) = rs 1 c (aC z) := by
    intro c
    simp only [haC, map_sub, map_sum]
    rw [(hHR C d I κ X _ z cX cz c).2, Finset.sum_congr rfl fun k _ => (hHR C d I κ X _ z (rc_cc cγ (ζ ^ k)) cz c).2]
  have brs : ∀ c : C, bC (rc c γ) = rs 0 c (bC γ) := by
    intro c
    simp only [hbC, map_sub, map_sum]
    rw [(hHR C d I κ X γ _ cγ cZ c).1, Finset.sum_congr rfl fun k _ => (hHR C d I κ X γ _ cγ (rc_cc cz (ζ ^ k)) c).1]
  set Aa := mvExp (aC z) with hAa
  set Bb := mvExp (bC γ) with hBb
  set A1 := mvExp (bC (pw (V.l ^ 2) δ)) with hA1
  set A2 := mvExp (aC (pw V.l ε)) with hA2
  set B1 := ∏ k ∈ Finset.range V.l, rs 1 (ζ ^ k) Aa with hB1
  set B2 := ∏ k ∈ Finset.range V.l, rs 0 (ζ ^ k) Bb with hB2
  have hE' : A1 * B1 = A2 * B2 := by
    have e1 : ∏ k ∈ Finset.range V.l, mvExp (aC (rc (ζ ^ k) z)) = B1 :=
      Finset.prod_congr rfl fun k _ => by rw [ars, mvExp_rs]
    have e2 : ∏ k ∈ Finset.range V.l, mvExp (bC (rc (ζ ^ k) γ)) = B2 :=
      Finset.prod_congr rfl fun k _ => by rw [brs, mvExp_rs]
    rw [← e1, ← e2]
    exact hE
  have iAa : IntS V Aa := (hHI C V d I κ X hb hBi ζ hζ1 (V.l ^ 2) hll γ δ z hγ hδ hz hrel).1
  have iBb : IntS V Bb := (hHI C V d I κ X hb hBi ζ hζ1 V.l hl0 z ε γ hz hε hγ hrel').2
  have rB1 := hRo C V ζ hζ1 1 Aa iAa
  have rB2 := hRo C V ζ hζ1 0 Bb iBb
  have iB1 : IntS V B1 := by
    intro μ
    have := (ge_of_mm (rB1 μ)).add (IntS.pow iAa V.l μ)
    rwa [← map_add, sub_add_cancel] at this
  have hμ0 : V.l • ee V.l 1 = ee (V.l ^ 2) V.l := by rw [smul_ee, mul_one, sq]
  have one0 : ∀ i j : ℕ, j ≠ 0 → coeff (ee i j) (1 : MvPowerSeries (Fin 2) C) = 0 := by
    intro i j hj
    rw [MvPowerSeries.coeff_one, if_neg (ee_ne hj)]

  have cAa : coeff (ee V.l 1) Aa = PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) := by
    rw [hAa, hEx C (aC z) 1 le_rfl (aK z 1 le_rfl (low1 z cz)).1 V.l 1 (by omega), one0 _ _ one_ne_zero, zero_add,
      (aK z 1 le_rfl (low1 z cz)).2]
  have lowerFactorEntryConstant : V.MM (coeff (ee (V.l ^ 2) V.l) B1 -
      PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l) := by
    have h1 := rB1 (ee (V.l ^ 2) V.l)
    have h2 := hFr C V (Fin 2) Aa iAa (ee V.l 1)
    rw [hμ0, cAa] at h2
    have := mm_add h1 h2
    rwa [map_sub, sub_add_sub_cancel] at this

  have cBb : coeff (ee V.l 1) Bb = 0 := by
    rw [hBb, hEx C (bC γ) 1 le_rfl (fun i j hj => by
      obtain rfl : j = 0 := by omega
      exact (bK γ cγ).1 i) V.l 1 (by omega), one0 _ _ one_ne_zero, zero_add, (bK γ cγ).2]
  have cB2 : V.MM (coeff (ee (V.l ^ 2) V.l) B2) := by
    have h1 := rB2 (ee (V.l ^ 2) V.l)
    have h2 := hFr C V (Fin 2) Bb iBb (ee V.l 1)
    rw [hμ0, cBb, zero_pow hl0.ne', sub_zero] at h2
    have := mm_add h1 h2
    rwa [map_sub, sub_add_cancel] at this
  have kB2 : ∀ i j, j < 1 → coeff (ee i j) (B2 - 1) = 0 := by
    intro i j hj
    have e2 : B2 = mvExp (∑ k ∈ Finset.range V.l, bC (rc (ζ ^ k) γ)) := by
      rw [Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun k _ => ccb _ (rc_cc cγ _))]
      exact Finset.prod_congr rfl fun k _ => by rw [brs, mvExp_rs]
    have hK : ∀ i j, j < 1 → coeff (ee i j) (∑ k ∈ Finset.range V.l, bC (rc (ζ ^ k) γ)) = 0 := by
      intro i j hj
      obtain rfl : j = 0 := by omega
      rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => (bK _ (rc_cc cγ _)).1 i
    rw [map_sub, e2, hEx C _ 1 le_rfl hK i j (by omega), hK i j hj, add_zero, sub_self]

  have lowZ := pw_low cε hl0
  have cA2 : coeff (ee (V.l ^ 2) V.l) A2 =
      PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (ε i)) := by
    rw [hA2, hEx C _ V.l hl0 (aK _ V.l hl0 lowZ).1 (V.l ^ 2) V.l (by omega), one0 _ _ hl0.ne', zero_add,
      (aK _ V.l hl0 lowZ).2]
    congr 2
    funext i
    exact pw_lead ε hl0 i
  have kA2 : ∀ i j, j < V.l → coeff (ee i j) (A2 - 1) = 0 := by
    intro i j hj
    rw [map_sub, hA2, hEx C _ V.l hl0 (aK _ V.l hl0 lowZ).1 i j (by omega), (aK _ V.l hl0 lowZ).1 i j hj, add_zero,
      sub_self]

  have jA1 : ∀ i j, i ≤ V.l ^ 2 → V.MM (coeff (ee i j) (A1 - 1)) :=
    hGe C V d I κ X hb hBi ζ hζ1 V.l hl0 z ε δ hz hε hδ hrel' hmm (V.l ^ 2) hll
  have hL : coeff (ee (V.l ^ 2) V.l) (A1 * B1) =
      coeff (ee (V.l ^ 2) V.l) B1 + coeff (ee (V.l ^ 2) V.l) ((A1 - 1) * B1) := by
    rw [← map_add]
    congr 1
    ring
  have hR : coeff (ee (V.l ^ 2) V.l) (A2 * B2) = coeff (ee (V.l ^ 2) V.l) A2 + coeff (ee (V.l ^ 2) V.l) B2 := by
    have e : A2 * B2 = A2 + B2 - 1 + (A2 - 1) * (B2 - 1) := by ring
    rw [e, map_add, map_sub, map_add, one0 _ _ hl0.ne', kmul kA2 kB2 _ _ (by omega), sub_zero, add_zero]
  have hJ := jmul jA1 iB1 (V.l ^ 2) V.l le_rfl
  rw [hE', hR, cA2] at hL
  have fin : PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l -
      PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (ε i)) =
      -(coeff (ee (V.l ^ 2) V.l) B1 -
        PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l) +
      (coeff (ee (V.l ^ 2) V.l) B2 - coeff (ee (V.l ^ 2) V.l) ((A1 - 1) * B1)) := by
    linear_combination (-1 : C) * hL
  rw [fin]
  exact mm_add (mm_neg lowerFactorEntryConstant) (mm_sub cB2 hJ)

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds SelfConjCharts MvPowerSeries

theorem r1sExpLow_holds : ExpLowOrderTruncation := by
  intro C _ _ F m hm hK i j hj
  have h2 : ∀ k, coeff (ee i j) (F ^ (k + 1 + 1)) = 0 := by
    intro k
    have e : F ^ (k + 1 + 1) = (F * F) * F ^ k := by ring
    rw [e]
    exact kmul (a := 2 * m) (b := 0) (fun i j h => kmul hK hK i j (by omega))
      (fun _ _ h => absurd h (Nat.not_lt_zero _)) i j (by omega)
  show ∑ k ∈ Finset.range ((ee i j).degree + 1), coeff (ee i j) (F ^ k) / (k.factorial : C) = _
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [add_comm]
  congr 1
  cases hd : (ee i j).degree with
  | zero =>
    rw [Finset.sum_range_zero]
    have h0 : ee i j = 0 := (Finsupp.degree_eq_zero_iff _).1 hd
    have hj0 : j = 0 := by
      have := DFunLike.congr_fun h0 1
      simpa [ee_one] using this
    exact (hK i j (by omega)).symm
  | succ n =>
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun k _ => by rw [h2 k, zero_div])]
    simp

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sFrob_holds : PowerSeriesFrobeniusCongruence := frobPow_smul

theorem r1sRoots_holds : RootsOfUnityProductCongruence := fun C _ V ζ hζ j f hf μ => rootsProd C V ζ hζ j f hf μ

theorem coeffIdentity_selfConj_of_four_open (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry) (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four good_curve_closed r1sRestB_holds
    (r1sRestC_of r1sFrob_holds r1sRoots_holds r1sExpLow_holds hHL hHR hHI hGe) biadditive_on_columns

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjGauge

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def IsPt (V : VF C) {τ : Type} (a : κ → MvPowerSeries τ C) : Prop :=
  ∀ i, MvPowerSeries.constantCoeff (a i) = 0 ∧ IntS V (a i)

def BiInt (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ (τ : Type) [Finite τ] (n : ℕ) (a : ℕ → κ → MvPowerSeries τ C) (s c : κ → MvPowerSeries τ C),
    (∀ k, IsPt V (a k)) → IsPt V s → IsPt V c →
    (∀ i, MvPowerSeries.subst s (X.lg i) = ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (X.lg i)) →
    IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range n, hAt X (a k) c - hAt X s c)) ∧
      IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range n, hAt X c (a k) - hAt X c s))

def NormRel (X : RawChart C d I κ) (l n : ℕ) (ζ : C) (γ δ : κ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) =
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i))

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

def pw (n : ℕ) (δ : κ → PowerSeries C) : κ → PowerSeries C :=
  fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (δ i)

section Lem

variable {V : VF C}

theorem intS_of_ps {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) : IntS V f := fun μ => by
  have hμ : μ = Finsupp.single () (μ ()) := Finsupp.ext fun u => by cases u; simp
  rw [hμ]; exact hf (μ ())

theorem ps_of_intS {f : PowerSeries C} (hf : IntS V f) : ∀ n, V.Ge 0 (PowerSeries.coeff n f) :=
  fun n => hf (Finsupp.single () n)

theorem subst_ps {τ : Type} {a : MvPowerSeries τ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hai : IntS V a) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 ∧ IntS V (PowerSeries.subst a f) := by
  refine ⟨constantCoeff_subst_zero (σ := Unit) (fun _ => ha) hf0, ?_⟩
  exact PartialDerivEval.intS_subst (fun _ => ha) (fun _ => hai) (intS_of_ps hf)

theorem inV_pt (j : Fin 2) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) :
    MvPowerSeries.constantCoeff (inV j f) = 0 ∧ IntS V (inV j f) :=
  subst_ps (MvPowerSeries.constantCoeff_X j) (PartialDerivEval.intS_X j) hf0 hf

theorem rc_cv {c : C} (hc : V.Ge 0 c) {γ : κ → PowerSeries C} (hγ : IsCv V γ) : IsCv V (rc c γ) := by
  intro i
  refine ⟨?_, fun n => ?_⟩
  · show PowerSeries.constantCoeff (PowerSeries.rescale c (γ i)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (hγ i).1]
  · show V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale c (γ i)))
    rw [PowerSeries.coeff_rescale]
    exact (hc.pow n).mul_int ((hγ i).2 n)

theorem pw_cv {n : ℕ} (hn : 0 < n) {δ : κ → PowerSeries C} (hδ : IsCv V δ) : IsCv V (pw n δ) := by
  intro i
  have hX : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ n) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
  have hXi : IntS V ((PowerSeries.X : PowerSeries C) ^ n) :=
    PartialDerivEval.intS_pow (intS_of_ps fun m => by
      rw [PowerSeries.coeff_X]; split_ifs; exacts [VF.Ge.one, VF.Ge.zero 0]) n
  obtain ⟨h0, hI⟩ := subst_ps (τ := Unit) hX hXi (hδ i).1 (hδ i).2
  exact ⟨h0, ps_of_intS hI⟩

theorem subst_inV (j : Fin 2) {x : κ → PowerSeries C} (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun i => inV j (x i)) F = inV j (alongCv x F) := by
  unfold inV alongCv
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hx)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ : Unit => MvPowerSeries.constantCoeff_X j))]

theorem inV_sum (j : Fin 2) {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) :
    inV j (∑ k ∈ s, f k) = ∑ k ∈ s, inV j (f k) := by
  unfold inV
  have hS : PowerSeries.HasSubst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X j)
  rw [← PowerSeries.coe_substAlgHom hS, map_sum]

theorem log_rel (X : RawChart C d I κ) (j : Fin 2) {l n : ℕ} (hn : 0 < n) {ζ : C} {γ δ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0)
    (hN : NormRel X l n ζ γ δ) (i : κ) :
    MvPowerSeries.subst (fun i => inV j (pw n δ i)) (X.lg i) =
      ∑ k ∈ Finset.range l, MvPowerSeries.subst (fun i => inV j (rc (ζ ^ k) γ i)) (X.lg i) := by
  have hX : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ n) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
  have hpw0 : ∀ i, PowerSeries.constantCoeff (pw n δ i) = 0 := fun i =>
    constantCoeff_subst_zero (σ := Unit) (fun _ => hX) (hδ i)
  have hrc0 : ∀ (c : C) i, PowerSeries.constantCoeff (rc c γ i) = 0 := fun c i => by
    show PowerSeries.constantCoeff (PowerSeries.rescale c (γ i)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ i]
  rw [subst_inV j hpw0]
  simp only [subst_inV j (hrc0 _)]
  rw [← inV_sum]
  congr 1
  rw [show alongCv (pw n δ) (X.lg i) = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) from
    alongCv_repar hδ hX (X.lg i), hN i]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : PowerSeries.constantCoeff ((ζ ^ k) • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  show PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i)) = alongCv (fun i => PowerSeries.rescale (ζ ^ k) (γ i)) (X.lg i)
  rw [PowerSeries.rescale_eq_subst]
  simp only [PowerSeries.rescale_eq_subst]
  rw [alongCv_repar hγ hc]

end Lem

theorem hInt_core [CharZero C] (V : VF C) (X : RawChart C d I κ) (hBi : BiInt X V) (ζ : C) (hζ : ζ ^ V.l = 1)
    (n : ℕ) (hn : 0 < n) (γ δ c : κ → PowerSeries C) (hγ : IsCv V γ) (hδ : IsCv V δ) (hc : IsCv V c)
    (hN : NormRel X V.l n ζ γ δ) :
    IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw n δ) c)) ∧
      IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) γ) - HH X c (pw n δ))) := by
  have hζint : V.Ge 0 ζ := V.ge_of_pow_eq_one V.l_prime.ne_zero hζ
  have hrc : ∀ k, IsCv V (rc (ζ ^ k) γ) := fun k => rc_cv (hζint.pow k) hγ
  have hpw : IsCv V (pw n δ) := pw_cv hn hδ
  have pt : ∀ (j : Fin 2) (x : κ → PowerSeries C), IsCv V x → IsPt V (fun i => inV j (x i)) :=
    fun j x hx i => inV_pt j (hx i).1 (hx i).2
  refine ⟨?_, ?_⟩
  · exact (hBi (Fin 2) V.l (fun k i => inV 0 (rc (ζ ^ k) γ i)) (fun i => inV 0 (pw n δ i))
      (fun i => inV 1 (c i)) (fun k => pt 0 _ (hrc k)) (pt 0 _ hpw) (pt 1 _ hc)
      (log_rel X 0 hn (fun i => (hγ i).1) (fun i => (hδ i).1) hN)).1
  · exact (hBi (Fin 2) V.l (fun k i => inV 1 (rc (ζ ^ k) γ i)) (fun i => inV 1 (pw n δ i))
      (fun i => inV 0 (c i)) (fun k => pt 1 _ (hrc k)) (pt 1 _ hpw) (pt 0 _ hc)
      (log_rel X 1 hn (fun i => (hγ i).1) (fun i => (hδ i).1) hN)).2

end SelfConjGauge

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjPoints

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def ee (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

theorem hsX (j : Fin 2) : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem inV_cc (j : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (inV j f) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hf

theorem rescale_inV (w : Fin 2 → C) (j : Fin 2) (f : PowerSeries C) :
    MvPowerSeries.rescale w (inV j f) = inV j (PowerSeries.rescale (w j) f) := by
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have hc : MvPowerSeries.HasSubst (fun _ : Unit => (w j • PowerSeries.X : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by
      show MvPowerSeries.constantCoeff (w j • (PowerSeries.X : PowerSeries C)) = 0
      rw [MvPowerSeries.smul_eq_C_mul, map_mul,
        show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries C) = 0 from MvPowerSeries.constantCoeff_X (), mul_zero]
  unfold inV
  rw [MvPowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (hsX j) hw, MvPowerSeries.subst_comp_subst_apply hc (hsX j)]
  congr 1
  funext u
  rw [MvPowerSeries.subst_X hw, ← MvPowerSeries.coe_substAlgHom (hsX j), map_smul, MvPowerSeries.coe_substAlgHom (hsX j)]
  have h1 : MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) (PowerSeries.X : PowerSeries C) =
      MvPowerSeries.X j := MvPowerSeries.subst_X (hsX j) ()
  rw [h1]
  rfl

theorem rescale_HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (w : Fin 2 → C) :
    MvPowerSeries.rescale w (HH X x z) = HH X (rc (w 0) x) (rc (w 1) z) := by
  have hP : MvPowerSeries.HasSubst (pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (z i))) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ?_
    unfold pairSubst
    split_ifs
    · exact inV_cc 0 (hx q.2)
    · exact inV_cc 1 (hz q.2)
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold HH hAt
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hP hw]
  congr 1
  funext q
  rw [← MvPowerSeries.rescale_eq_subst]
  unfold pairSubst rc
  split_ifs
  · exact rescale_inV w 0 (x q.2)
  · exact rescale_inV w 1 (z q.2)

end SelfConjPoints

open SelfConjPoints in

theorem r1sHResc (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (c : C) :
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z) := by
  have e1 : ∀ y : κ → PowerSeries C, rc 1 y = y := fun y => by
    funext i; unfold rc; rw [PowerSeries.rescale_one]; rfl
  refine ⟨?_, ?_⟩
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sHInt_holds : IntegralUnitFamilies :=
  fun C _ _ V d I _ κ _ X _ hBi ζ hζ n hn γ δ c hγ hδ hc hN => SelfConjGauge.hInt_core V X hBi ζ hζ n hn γ δ c hγ hδ hc hN

theorem r1sHResc_holds : GaugeRescalingSymmetry := r1sHResc

theorem coeffIdentity_selfConj_of_two (hHL : GaugeLeadingTermLinear) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four_open hHL r1sHResc_holds r1sHInt_holds hGe

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MvPowerSeries

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def Kd (r : ℕ) (f : MvPowerSeries (Fin 2) C) : Prop := ∀ i j, j < r → coeff (ee i j) f = 0

theorem Kd.mul {a b : ℕ} {f g : MvPowerSeries (Fin 2) C} (hf : Kd a f) (hg : Kd b g) : Kd (a + b) (f * g) :=
  fun i j h => kmul hf hg i j h

theorem Kd.zero' (f : MvPowerSeries (Fin 2) C) : Kd 0 f := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem Kd.pow {m : ℕ} {f : MvPowerSeries (Fin 2) C} (hf : Kd m f) (k : ℕ) : Kd (m * k) (f ^ k) := by
  induction k with
  | zero => exact Kd.zero' _
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hf

def zdeg (e : Fin 2 × κ →₀ ℕ) : ℕ := ∑ i, e (1, i)

theorem zdeg_add (e e' : Fin 2 × κ →₀ ℕ) : zdeg (e + e') = zdeg e + zdeg e' := by
  unfold zdeg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem zdeg_single1 (i : κ) (k : ℕ) : zdeg (Finsupp.single ((1 : Fin 2), i) k) = k := by
  unfold zdeg
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (Prod.mk.inj h).2.symm
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem Kd_prod {a : Fin 2 × κ → MvPowerSeries (Fin 2) C} {m : ℕ} (ha : ∀ i, Kd m (a (1, i)))
    (e : Fin 2 × κ →₀ ℕ) : Kd (m * zdeg e) (e.prod fun s k => a s ^ k) := by
  induction e using Finsupp.induction_linear with
  | zero =>
    have : zdeg (0 : Fin 2 × κ →₀ ℕ) = 0 := by simp [zdeg]
    rw [this, mul_zero]
    exact Kd.zero' _
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), zdeg_add, mul_add]
    exact hf.mul hg
  | single s k =>
    rw [Finsupp.prod_single_index (h := fun s k => a s ^ k) (pow_zero _)]
    obtain ⟨g, i⟩ := s
    by_cases hg : g = 1
    · subst hg
      rw [zdeg_single1]
      exact (ha i).pow k
    · have : zdeg (Finsupp.single (g, i) k) = 0 := by
        unfold zdeg
        apply Finset.sum_eq_zero
        intro b _
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hg (Prod.mk.inj h).1
      rw [this, mul_zero]
      exact Kd.zero' _

theorem Kd_subst {a : Fin 2 × κ → MvPowerSeries (Fin 2) C} (ha0 : ∀ s, constantCoeff (a s) = 0) {m : ℕ}
    (ha : ∀ i, Kd m (a (1, i))) {f : MvPowerSeries (Fin 2 × κ) C} {r : ℕ} (hf : ∀ e, zdeg e < r → coeff e f = 0) :
    Kd (m * r) (subst a f) := by
  intro i j hj
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : zdeg e < r
  · rw [hf e he, zero_smul]
  · rw [Kd_prod ha e i j (lt_of_lt_of_le hj (Nat.mul_le_mul_left m (not_lt.1 he))), smul_zero]

theorem ee_eq_single0 {a b k : ℕ} : ee a b = Finsupp.single 0 k ↔ a = k ∧ b = 0 := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    rw [ee_zero] at h0
    rw [ee_one] at h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [ee]

theorem ee_eq_single1 {a b k : ℕ} : ee a b = Finsupp.single 1 k ↔ a = 0 ∧ b = k := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    rw [ee_zero] at h0
    rw [ee_one] at h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [ee]

theorem coeff_embedFirstVar (a b : ℕ) (f : PowerSeries C) :
    coeff (ee a b) (inV 0 f) = if b = 0 then PowerSeries.coeff a f else 0 := by
  unfold inV
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X 0))]
  simp only [coeff_X_pow, ee_eq_single0]
  by_cases hb : b = 0
  · rw [if_pos hb, finsum_eq_single _ a]
    · simp [hb]
    · intro k hk
      rw [if_neg (fun h => hk h.1.symm), smul_zero]
  · rw [if_neg hb]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [if_neg (fun h => hb h.2), smul_zero]

theorem coeff_embedSecondVar (a b : ℕ) (f : PowerSeries C) :
    coeff (ee a b) (inV 1 f) = if a = 0 then PowerSeries.coeff b f else 0 := by
  unfold inV
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X 1))]
  simp only [coeff_X_pow, ee_eq_single1]
  by_cases ha : a = 0
  · rw [if_pos ha, finsum_eq_single _ b]
    · simp [ha]
    · intro k hk
      rw [if_neg (fun h => hk h.2.symm), smul_zero]
  · rw [if_neg ha]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [if_neg (fun h => ha h.1), smul_zero]

theorem coeff_inV_mul (n j : ℕ) (P Q : PowerSeries C) :
    coeff (ee n j) (inV 1 P * inV 0 Q) = PowerSeries.coeff j P * PowerSeries.coeff n Q := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (ee 0 j, ee n 0)]
  · rw [coeff_embedSecondVar, coeff_embedFirstVar, if_pos rfl, if_pos rfl]
  · rintro ⟨p, q⟩ hpq hne
    have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
    have e0 : p 0 + q 0 = n := by
      have := DFunLike.congr_fun e 0
      simpa [ee_zero] using this
    have e1 : p 1 + q 1 = j := by
      have := DFunLike.congr_fun e 1
      simpa [ee_one] using this
    show coeff p (inV 1 P) * coeff q (inV 0 Q) = 0
    rw [eq_ee p, eq_ee q, coeff_embedSecondVar, coeff_embedFirstVar]
    by_cases hp : p 0 = 0
    · by_cases hq : q 1 = 0
      · exfalso
        apply hne
        rw [eq_ee p, eq_ee q, hp, hq]
        have h1 : p 1 = j := by omega
        have h2 : q 0 = n := by omega
        rw [h1, h2]
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  · intro h
    exfalso
    apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext x
    fin_cases x <;> simp [ee]

def rho (F : MvPowerSeries κ C) : MvPowerSeries (Fin 2 × κ) C :=
  subst (fun x : κ => (X ((0 : Fin 2), x) : MvPowerSeries (Fin 2 × κ) C)) F

def h2 (X : RawChart C d I κ) : MvPowerSeries (Fin 2 × κ) C :=
  X.h + ∑ i, MvPowerSeries.X ((1 : Fin 2), i) * rho (X.sg (Pi.single i 1))

theorem iota_inj : Function.Injective (fun x : κ => ((0 : Fin 2), x)) := fun _ _ h => (Prod.mk.inj h).2

theorem coeff_X_mul_rho (i : κ) (F : MvPowerSeries κ C) (e : Fin 2 × κ →₀ ℕ) (h : e (1, i) = 0) :
    coeff e (MvPowerSeries.X ((1 : Fin 2), i) * rho F) = 0 := by
  rw [X_def, coeff_monomial_mul, if_neg]
  intro hle
  have := hle (1, i)
  rw [Finsupp.single_eq_same, h] at this
  omega

theorem coeff_gaugeSquare_low_degree (X : RawChart C d I κ)
    (hax : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → coeff e X.h = 0) (e : Fin 2 × κ →₀ ℕ)
    (he : zdeg e < 2) : coeff e (h2 X) = 0 := by
  unfold h2
  rw [map_add, map_sum]
  by_cases h0 : ∀ i, e (1, i) = 0
  · rw [Finset.sum_eq_zero fun i _ => coeff_X_mul_rho i _ e (h0 i), add_zero]
    apply hax
    rintro ⟨g, i⟩ hs hg
    simp only at hg
    subst hg
    exact (Finsupp.mem_support_iff.1 hs) (h0 i)
  · push Not at h0
    obtain ⟨i0, hi0⟩ := h0
    have hsum : e (1, i0) + ∑ i ∈ Finset.univ.erase i0, e (1, i) = zdeg e :=
      Finset.add_sum_erase Finset.univ (fun i => e (1, i)) (Finset.mem_univ i0)
    have h1 : e (1, i0) = 1 := by omega
    have hrest : ∑ i ∈ Finset.univ.erase i0, e (1, i) = 0 := by omega
    have hoth : ∀ i, i ≠ i0 → e (1, i) = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff.1 hrest) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    rw [Finset.sum_eq_single i0 (fun i _ hi => coeff_X_mul_rho i _ e (hoth i hi))
      (fun h => absurd (Finset.mem_univ i0) h)]
    have hle : Finsupp.single ((1 : Fin 2), i0) 1 ≤ e := by
      intro s
      by_cases hs : s = (1, i0)
      · subst hs; rw [Finsupp.single_eq_same, h1]
      · rw [Finsupp.single_apply, if_neg (fun h => hs h.symm)]; exact Nat.zero_le _
    rw [X_def, coeff_monomial_mul, if_pos hle, one_mul]
    set e' := e - Finsupp.single ((1 : Fin 2), i0) 1 with he'
    have hee : e' + Finsupp.single ((1 : Fin 2), i0) 1 = e := tsub_add_cancel_of_le hle
    have hran : (↑e'.support : Set (Fin 2 × κ)) ⊆ Set.range (fun x : κ => ((0 : Fin 2), x)) := by
      rintro ⟨g, i⟩ hs
      have hs' : e' (g, i) ≠ 0 := Finsupp.mem_support_iff.1 hs
      rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
      · exact ⟨i, rfl⟩
      · exfalso
        apply hs'
        rw [he', Finsupp.tsub_apply]
        by_cases hi : i = i0
        · subst hi; rw [Finsupp.single_eq_same, h1]
        · rw [hoth i hi]; simp
    have hmap := Finsupp.mapDomain_comapDomain (fun x : κ => ((0 : Fin 2), x)) iota_inj e' hran
    unfold rho
    rw [← hmap, coeff_subst_rename_inj _ iota_inj]
    show coeff e X.h + -∑ j, (Pi.single i0 (1 : C) : κ → C) j * coeff _ X.h = 0
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i0) h), Pi.single_eq_same, one_mul, hmap, hee, add_neg_cancel]

end SelfConjCharts

open SelfConjCharts MvPowerSeries

theorem r1sHLin_holds : GaugeLeadingTermLinear := by
  intro C _ d I _ κ _ X hax x c hx m hm hc
  set a : Fin 2 × κ → MvPowerSeries (Fin 2) C := pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (c i)) with ha
  have hc0 : ∀ i, PowerSeries.constantCoeff (c i) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hc i 0 (by omega)
  have cc0 : ∀ (j : Fin 2) (f : PowerSeries C), PowerSeries.constantCoeff f = 0 → constantCoeff (inV j f) = 0 := by
    intro j f hf
    rw [← coeff_zero_eq_constantCoeff_apply, ← ee_00]
    fin_cases j
    · show coeff (ee 0 0) (inV 0 f) = 0
      rw [coeff_embedFirstVar, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    · show coeff (ee 0 0) (inV 1 f) = 0
      rw [coeff_embedSecondVar, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  have ha0 : ∀ s, constantCoeff (a s) = 0 := by
    rintro ⟨g, i⟩
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact cc0 0 _ (hx i)
    · exact cc0 1 _ (hc0 i)
  have haK : ∀ i, Kd m (a (1, i)) := by
    intro i n j hj
    show coeff (ee n j) (inV 1 (c i)) = 0
    rw [coeff_embedSecondVar]
    split_ifs
    · exact hc i j hj
    · rfl
  have hS := hasSubst_of_constantCoeff_zero ha0
  have hdec : HH X x c = subst a (h2 X) - ∑ i, inV 1 (c i) * inV 0 (alongCv x (X.sg (Pi.single i 1))) := by
    have e1 : subst a (h2 X) = subst a X.h + ∑ i, a (1, i) * subst a (rho (X.sg (Pi.single i 1))) := by
      unfold h2
      rw [subst_add hS]
      congr 1
      rw [← substAlgHom_apply hS, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [substAlgHom_apply hS, subst_mul hS, subst_X hS]
    have e2 : ∀ F : MvPowerSeries κ C, subst a (rho F) = inV 0 (alongCv x F) := by
      intro F
      unfold SelfConjCharts.rho
      rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hS]
      simp only [subst_X hS]
      exact SelfConjGauge.subst_inV 0 hx F
    simp only [e2] at e1
    rw [e1]
    show subst a X.h = _
    have : ∀ i, a (1, i) = inV 1 (c i) := fun i => rfl
    simp only [this]
    ring
  have hK2 : Kd (m * 2) (subst a (h2 X)) := Kd_subst ha0 haK (coeff_gaugeSquare_low_degree X hax)
  constructor
  · intro n j hj
    rw [hdec, map_sub, hK2 n j (by omega), map_sum, zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_inV_mul, hc i j hj, zero_mul]
  · intro n
    rw [hdec, map_sub, hK2 n m (by omega), map_sum, zero_sub]
    congr 1
    simp only [coeff_inV_mul]
    have hv : (fun i => PowerSeries.coeff m (c i)) =
        fun k => ∑ q, PowerSeries.coeff m (c q) * (Pi.single q (1 : C) : κ → C) k := by
      funext k
      rw [Finset.sum_eq_single k (fun q _ hq => by rw [Pi.single_eq_of_ne (Ne.symm hq), mul_zero])
        (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
    rw [hv, sg_lin, alongCv_lin hx, map_sum]
    simp only [PowerSeries.coeff_smul, smul_eq_mul]

end Formalism.L2.FormalSeriesBounds
end
end
