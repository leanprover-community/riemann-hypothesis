import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries

noncomputable section

section PowerSeriesAgreement

variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}

def PTAgree (k : ℕ) (A A' : ι → MvPowerSeries τ R) : Prop :=
  ∀ i (e : τ →₀ ℕ), e.degree < k → coeff e (A i) = coeff e (A' i)

theorem PTAgree.mono {k l : ℕ} {A A' : ι → MvPowerSeries τ R} (h : PTAgree k A A') (hl : l ≤ k) :
    PTAgree l A A' := fun i e he => h i e (lt_of_lt_of_le he hl)

theorem PTAgree.trans {k : ℕ} {A B D : ι → MvPowerSeries τ R} (h : PTAgree k A B)
    (h' : PTAgree k B D) : PTAgree k A D := fun i e he => (h i e he).trans (h' i e he)

theorem PTAgree.symm {k : ℕ} {A B : ι → MvPowerSeries τ R} (h : PTAgree k A B) :
    PTAgree k B A := fun i e he => (h i e he).symm

theorem ptAgree_zero (A A' : ι → MvPowerSeries τ R) : PTAgree 0 A A' :=
  fun _ _ he => absurd he (Nat.not_lt_zero _)

theorem PTAgree.eq {A A' : ι → MvPowerSeries τ R} (h : ∀ k, PTAgree k A A') : A = A' :=
  funext fun i => MvPowerSeries.ext fun e => h (e.degree + 1) i e (Nat.lt_succ_self _)

section Fixed

variable (T : (ι → MvPowerSeries τ R) → (ι → MvPowerSeries τ R))
  (P : (ι → MvPowerSeries τ R) → Prop)

theorem pt_unique
    (hT : ∀ k x y, P x → P y → PTAgree k x y → PTAgree (k + 1) (T x) (T y))
    {x y : ι → MvPowerSeries τ R} (hx : P x) (hy : P y) (hTx : T x = x) (hTy : T y = y) :
    x = y := by
  refine ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.eq fun k => ?_
  induction k with
  | zero => exact ptAgree_zero _ _
  | succ k ih =>
    have h := hT k x y hx hy ih
    rwa [hTx, hTy] at h

end Fixed

section Order

private theorem natCast_le_order_iff_coeff_eq_zero {f : MvPowerSeries τ R} {n : ℕ} :
    (n : ℕ∞) ≤ f.order ↔ ∀ d : τ →₀ ℕ, d.degree < n → coeff d f = 0 :=
  ⟨fun h _ hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h), nat_le_order⟩

private theorem natCast_le_order_add {f g : MvPowerSeries τ R} {n : ℕ}
    (hf : (n : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) : (n : ℕ∞) ≤ (f + g).order :=
  natCast_le_order_iff_coeff_eq_zero.2 fun d hd => by
    rw [map_add, natCast_le_order_iff_coeff_eq_zero.1 hf d hd, natCast_le_order_iff_coeff_eq_zero.1 hg d hd, add_zero]

private theorem natCast_add_le_order_mul {f g : MvPowerSeries τ R} {a b : ℕ}
    (hf : (a : ℕ∞) ≤ f.order) (hg : (b : ℕ∞) ≤ g.order) : ((a + b : ℕ) : ℕ∞) ≤ (f * g).order :=
  le_trans (by rw [Nat.cast_add]; exact add_le_add hf hg) le_order_mul

private theorem natCast_le_order_of_le {f : MvPowerSeries τ R} {a b : ℕ} (hab : a ≤ b)
    (h : (b : ℕ∞) ≤ f.order) : (a : ℕ∞) ≤ f.order :=
  le_trans (Nat.cast_le.mpr hab) h

private theorem one_le_order_of_constantCoeff_eq_zero {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    ((1 : ℕ) : ℕ∞) ≤ f.order := by
  refine nat_le_order fun d hd => ?_
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  subst hd0
  simpa using hf

private theorem natCast_le_order_pow_of_constantCoeff_eq_zero {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) (m : ℕ) :
    (m : ℕ∞) ≤ (f ^ m).order := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    exact natCast_add_le_order_mul ih (one_le_order_of_constantCoeff_eq_zero hf)

theorem pt_order_pow_sub {f g : MvPowerSeries τ R} {j : ℕ}
    (hfg : ((j + 1 : ℕ) : ℕ∞) ≤ (f - g).order) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (m : ℕ) : ((j + m : ℕ) : ℕ∞) ≤ (f ^ m - g ^ m).order := by
  induction m with
  | zero => simp [MvPowerSeries.order_zero]
  | succ m ih =>
    have key : f ^ (m + 1) - g ^ (m + 1) = f ^ m * (f - g) + (f ^ m - g ^ m) * g := by ring
    rw [key]
    refine natCast_le_order_add ?_ ?_
    · exact natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero hf m) hfg)
    · exact natCast_le_order_of_le (by omega)
        (natCast_add_le_order_mul ih (one_le_order_of_constantCoeff_eq_zero hg))

theorem pt_order_prod_pow {σ : Type*} (A : σ → MvPowerSeries τ R)
    (hA : ∀ s, constantCoeff (A s) = 0) (α : σ →₀ ℕ) (S : Finset σ) :
    ((∑ s ∈ S, α s : ℕ) : ℕ∞) ≤ (∏ s ∈ S, A s ^ α s).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA a) (α a)) ih

theorem pt_order_prod_sub {σ : Type*} {A A' : σ → MvPowerSeries τ R} {j : ℕ}
    (hA : ∀ s, constantCoeff (A s) = 0) (hA' : ∀ s, constantCoeff (A' s) = 0)
    (hAA : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order) (α : σ →₀ ℕ) (S : Finset σ) :
    ((j + ∑ s ∈ S, α s : ℕ) : ℕ∞) ≤
      (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MvPowerSeries.order_zero]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have key : A a ^ α a * ∏ s ∈ S, A s ^ α s - A' a ^ α a * ∏ s ∈ S, A' s ^ α s =
        (A a ^ α a - A' a ^ α a) * ∏ s ∈ S, A s ^ α s +
          A' a ^ α a * (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s) := by ring
    rw [key]
    refine natCast_le_order_add ?_ ?_
    · exact natCast_le_order_of_le (by omega)
        (natCast_add_le_order_mul (pt_order_pow_sub (hAA a) (hA a) (hA' a) (α a))
          (pt_order_prod_pow A hA α S))
    · exact natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA' a) (α a)) ih)

theorem pt_subst_agree {σ : Type*} {A A' : σ → MvPowerSeries τ R} (hA : HasSubst A)
    (hA' : HasSubst A') (hA0 : ∀ s, constantCoeff (A s) = 0)
    (hA0' : ∀ s, constantCoeff (A' s) = 0) (K : MvPowerSeries σ R) (k : ℕ)
    (hAA : ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A s) = coeff e (A' s))
    (hK : ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s) :
    ∀ e : τ →₀ ℕ, e.degree < k + 1 → coeff e (subst A K) = coeff e (subst A' K) := by
  intro e he
  rw [coeff_subst hA K e, coeff_subst hA' K e]
  refine finsum_congr fun α => ?_
  by_cases hα : coeff α K = 0
  · simp [hα]
  congr 1
  simp only [Finsupp.prod]
  rcases hK α hα with h2 | hsame
  · have hdeg : α.degree = ∑ s ∈ α.support, α s := Finsupp.degree_apply α
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have h1 := pt_order_prod_pow A hA0 α α.support
      have h1' := pt_order_prod_pow A' hA0' α α.support
      have hlt : ((e.degree : ℕ) : ℕ∞) < ((∑ s ∈ α.support, α s : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : e.degree < ∑ s ∈ α.support, α s)
      rw [coeff_of_lt_order (lt_of_lt_of_le hlt h1), coeff_of_lt_order (lt_of_lt_of_le hlt h1')]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hAA' : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order := fun s =>
        nat_le_order fun d hd => by rw [map_sub, hAA s d hd, sub_self]
      have h := pt_order_prod_sub hA0 hA0' hAA' α α.support
      have hlt : ((e.degree : ℕ) : ℕ∞) < ((j + ∑ s ∈ α.support, α s : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : e.degree < j + ∑ s ∈ α.support, α s)
      have hz := coeff_of_lt_order (lt_of_lt_of_le hlt h)
      rw [map_sub, sub_eq_zero] at hz
      exact hz
  · have hprod : ∏ s ∈ α.support, A s ^ α s = ∏ s ∈ α.support, A' s ^ α s :=
      Finset.prod_congr rfl fun s hs => by rw [hsame s hs]
    rw [hprod]

end Order

end PowerSeriesAgreement

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

section Int

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

def ptIntSub : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, v.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp [v.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add _ _)
  zero_mem' := by simp [v.map_zero]
  neg_mem' {a} ha := by simpa [Set.mem_ofPred_eq, v.map_neg] using ha

def ptIntSer (σ : Type*) : Subring (MvPowerSeries σ C) where
  carrier := {f | ∀ α, coeff α f ∈ ptIntSub v}
  mul_mem' {f g} hf hg α := by
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)
  one_mem' α := by
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {f g} hf hg α := by rw [map_add]; exact Subring.add_mem _ (hf α) (hg α)
  zero_mem' α := by rw [map_zero]; exact Subring.zero_mem _
  neg_mem' {f} hf α := by rw [map_neg]; exact Subring.neg_mem _ (hf α)

variable {v}

theorem ptMvIsInt_iff {σ : Type*} (f : MvPowerSeries σ C) : MvIsInt v f ↔ f ∈ ptIntSer v σ := Iff.rfl

theorem ptIsIntV_iff (x : C) : IsIntV v x ↔ x ∈ ptIntSub v := Iff.rfl

theorem ptPsIsInt_iff (f : PowerSeries C) : PsIsInt v f ↔ f ∈ ptIntSer v Unit := by
  unfold PsIsInt
  constructor
  · intro h α
    have hα : α = Finsupp.single () (α ()) := by
      ext
      exact Finsupp.single_eq_same.symm
    have h1 := h (α ())
    rw [hα]
    exact h1
  · intro h n
    exact h (Finsupp.single () n)

theorem ptIntSer_X {σ : Type*} (s : σ) : (X s : MvPowerSeries σ C) ∈ ptIntSer v σ := by
  intro α
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem ptIntSer_smul {σ : Type*} {c : C} (hc : c ∈ ptIntSub v) {f : MvPowerSeries σ C}
    (hf : f ∈ ptIntSer v σ) : c • f ∈ ptIntSer v σ := by
  intro α
  rw [map_smul, smul_eq_mul]
  exact Subring.mul_mem _ hc (hf α)

theorem ptIntSer_subst {σ τ : Type*} {A : σ → MvPowerSeries τ C} (hA : HasSubst A)
    (hAi : ∀ s, A s ∈ ptIntSer v τ) {f : MvPowerSeries σ C} (hf : f ∈ ptIntSer v σ) :
    subst A f ∈ ptIntSer v τ := by
  intro e
  rw [MvPowerSeries.coeff_subst hA f e]
  have hmem : ∀ d : σ →₀ ℕ, coeff d f • coeff e (d.prod fun s n => A s ^ n) ∈ ptIntSub v := by
    intro d
    rw [smul_eq_mul]
    refine Subring.mul_mem _ (hf d) ?_
    have hp : (d.prod fun s n => A s ^ n) ∈ ptIntSer v τ :=
      Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hAi s) _
    exact hp e
  have key : ∀ g : (σ →₀ ℕ) → C, (∀ i, g i ∈ ptIntSub v) → ∑ᶠ i, g i ∈ ptIntSub v := by
    intro g hg
    by_cases hfin : (Function.support g).Finite
    · rw [finsum_eq_sum g hfin]
      exact Subring.sum_mem _ fun i _ => hg i
    · rw [finsum_of_infinite_support hfin]
      exact Subring.zero_mem _
  exact key _ hmem





end Int

section Lin

variable {R : Type*} [CommRing R]

theorem pt_degree_eq_one {σ : Type*} {α : σ →₀ ℕ} (h : α.degree = 1) :
    ∃ s, α = Finsupp.single s 1 := by
  classical
  have hsum : ∑ i ∈ α.support, α i = 1 := h
  obtain ⟨s, hs⟩ : α.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  refine ⟨s, ?_⟩
  have hs0 : α s ≠ 0 := Finsupp.mem_support_iff.mp hs
  ext t
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same]
    have h1 : α t ≤ ∑ i ∈ α.support, α i :=
      Finset.single_le_sum (f := fun i => α i) (fun _ _ => Nat.zero_le _) hs
    omega
  · have hst : s ≠ t := Ne.symm hts
    simp only [Finsupp.single_apply, hst, hts, if_false]
    by_contra hne
    have ht : t ∈ α.support := Finsupp.mem_support_iff.mpr hne
    have hsub : ({s, t} : Finset _) ⊆ α.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h2 := Finset.sum_le_sum_of_subset (f := fun i => α i) hsub
    rw [Finset.sum_pair hst] at h2
    omega

private theorem vmul_lemma {ρ K : Type*} [CommRing K] {P Q : MvPowerSeries ρ K} {m n : ℕ}
    (hP : ∀ e : ρ →₀ ℕ, e.degree < m → coeff e P = 0)
    (hQ : ∀ e : ρ →₀ ℕ, e.degree < n → coeff e Q = 0) :
    ∀ e : ρ →₀ ℕ, e.degree < m + n → coeff e (P * Q) = 0 := by
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := by
    first
    | exact Finsupp.degree_add _ _
    | exact map_add _ _ _
  rw [hx'] at hdeg
  by_cases h1 : x.1.degree < m
  · rw [hP _ h1, zero_mul]
  · rw [hQ _ (by omega), mul_zero]

private theorem vzero_lemma_2 {ρ : Type*} {e : ρ →₀ ℕ} (h : e.degree = 0) : e = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff _).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h

private theorem vpow_lemma_3 {ρ K : Type*} [CommRing K] {A : MvPowerSeries ρ K}
    (hA : constantCoeff A = 0) (k : ℕ) :
    ∀ e : ρ →₀ ℕ, e.degree < k → coeff e (A ^ k) = 0 := by
  induction k with
  | zero => intro e he; omega
  | succ k ih =>
    rw [pow_succ]
    refine vmul_lemma ih ?_
    intro e he
    have h0 : e = 0 := vzero_lemma_2 (by omega)
    rw [h0, coeff_zero_eq_constantCoeff_apply, hA]

private theorem vprod_lemma_4 {ι ρ K : Type*} [CommRing K] {A : ι → MvPowerSeries ρ K}
    (hA : ∀ s, constantCoeff (A s) = 0) (d : ι →₀ ℕ) (T : Finset ι) :
    ∀ e : ρ →₀ ℕ, e.degree < ∑ s ∈ T, d s → coeff e (∏ s ∈ T, A s ^ d s) = 0 := by
  classical
  refine Finset.induction_on T (fun e he => by simp at he) (fun a T ha ih => ?_)
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact vmul_lemma (vpow_lemma_3 (hA a) (d a)) ih

theorem pt_coeff_single_subst {σ τ : Type*} [Fintype σ]
    {A : σ → MvPowerSeries τ R} (hA : HasSubst A) (hA0 : ∀ s, constantCoeff (A s) = 0)
    {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) (i : τ) :
    coeff (Finsupp.single i 1) (subst A f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single i 1) (A s) := by
  classical
  rw [MvPowerSeries.coeff_subst hA f (Finsupp.single i 1)]
  have hi1 : (Finsupp.single i 1 : τ →₀ ℕ).degree = 1 := by
    first
    | exact Finsupp.degree_single i 1
    | simp [Finsupp.degree]
  have hsupp : (Function.support fun d : σ →₀ ℕ =>
      coeff d f • coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e)) ⊆
      ↑(Finset.univ.image fun s : σ => Finsupp.single s 1) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    by_contra hns
    apply hd
    by_cases hd0 : d = 0
    · rw [hd0, coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have hdeg : 2 ≤ d.degree := by
        by_contra hlt
        have hne : d.degree ≠ 0 := fun h0 => hd0 (vzero_lemma_2 h0)
        have h1 : d.degree = 1 := by omega
        obtain ⟨s, hs⟩ := pt_degree_eq_one h1
        apply hns
        rw [hs]
        exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ s))
      have hlt : (Finsupp.single i 1 : τ →₀ ℕ).degree < d.degree := by omega
      have hz : coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e) = 0 :=
        vprod_lemma_4 hA0 d d.support _ hlt
      rw [hz, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (by simp)]
    simp only [pow_one, smul_eq_mul]
  · intro s _ t _ hst
    exact (Finsupp.single_left_inj one_ne_zero).mp hst

theorem pt_coeff_single_X {σ : Type*} (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  rw [coeff_X]
  by_cases h : s = t
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h ((Finsupp.single_left_inj one_ne_zero).mp h')

theorem pt_hK_of_low {σ τ : Type*} {K : MvPowerSeries σ R}
    (hK : ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α K = 0) (A A' : σ → MvPowerSeries τ R) :
    ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s := by
  intro α hα
  left
  by_contra h
  exact hα (hK α (by omega))

end Lin

section Law

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem pt_F_lin (G : LogFGL v d) (a : Fin d) (i : Fin d ⊕ Fin d) :
    coeff (Finsupp.single i 1) (G.F a) =
      (if i = Sum.inl a then 1 else 0) + (if i = Sum.inr a then 1 else 0) := by
  have hF : HasSubst G.F := by
    first
    | exact HasSubst.of_constantCoeff_zero G.F_const
    | exact hasSubst_of_constantCoeff_zero G.F_const
  have hX : ∀ e : Fin d → Fin d ⊕ Fin d,
      HasSubst (fun b => (X (e b) : MvPowerSeries (Fin d ⊕ Fin d) C)) := by
    intro e
    first
    | exact HasSubst.of_constantCoeff_zero fun b => constantCoeff_X _
    | exact hasSubst_of_constantCoeff_zero fun b => constantCoeff_X _
  have key := congrArg (coeff (Finsupp.single i 1)) (G.lg_F a)
  rw [map_add, pt_coeff_single_subst hF G.F_const (G.lg_const a),
    pt_coeff_single_subst (hX Sum.inl) (fun b => constantCoeff_X _) (G.lg_const a),
    pt_coeff_single_subst (hX Sum.inr) (fun b => constantCoeff_X _) (G.lg_const a)] at key
  simp only [G.lg_lin, pt_coeff_single_X, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  convert key

end Law

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def PTGood (v : AddValuation C (WithTop ℝ)) {ι τ : Type*} (x : ι → MvPowerSeries τ C) : Prop :=
  ∀ i, constantCoeff (x i) = 0 ∧ x i ∈ ptIntSer v τ

theorem ptGood_zero {ι τ : Type*} : PTGood v (0 : ι → MvPowerSeries τ C) := fun _ => ⟨map_zero _, zero_mem _⟩

theorem ptGood_lim {ι τ : Type*} {T : (ι → MvPowerSeries τ C) → (ι → MvPowerSeries τ C)}
    (hP : ∀ n, PTGood v (T^[n] 0)) (x : ι → MvPowerSeries τ C)
    (hx : ∀ n, PTAgree n x (T^[n] 0)) : PTGood v x := by
  intro i
  have hc : ∀ e, coeff e (x i) = coeff e ((T^[e.degree + 1] 0) i) :=
    fun e => hx (e.degree + 1) i e (Nat.lt_succ_self _)
  refine ⟨?_, ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hP _ i).1
  · show ∀ α, coeff α (x i) ∈ ptIntSub v
    intro α
    have h : ∀ β, coeff β ((T^[α.degree + 1] 0) i) ∈ ptIntSub v := (hP _ i).2
    rw [hc]
    exact h α

theorem pt_subst_lin_split {σ τ : Type*} [Fintype σ] {x : σ → MvPowerSeries τ C}
    (hx : HasSubst x) (Φ : MvPowerSeries σ C) (m : σ → C) :
    subst x Φ = ∑ a, m a • x a + subst x (Φ - ∑ a, m a • X a) := by
  have hs : subst x (∑ a, m a • X a : MvPowerSeries σ C) = ∑ a, m a • x a := by
    rw [← MvPowerSeries.coe_substAlgHom hx, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hx, MvPowerSeries.subst_smul hx, MvPowerSeries.subst_X hx]
  rw [MvPowerSeries.subst_sub hx, hs]
  abel

theorem pt_low_of_lin {σ : Type*} [Fintype σ] {Φ : MvPowerSeries σ C}
    (h0 : constantCoeff Φ = 0) (m : σ → C)
    (hm : ∀ s, coeff (Finsupp.single s 1) Φ = m s) :
    ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α (Φ - ∑ a, m a • X a) = 0 := by
  intro α hα
  rw [map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hα with h | h
  · obtain rfl := (Finsupp.degree_eq_zero_iff α).mp h
    simp [MvPowerSeries.coeff_X, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    refine Finset.sum_eq_zero fun a _ => if_neg ?_
    exact fun e => (Finsupp.single_ne_zero.mpr one_ne_zero) e.symm
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hne
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    have hle : Finsupp.single s 1 ≤ α := by
      rw [Finsupp.le_def]
      intro i
      by_cases hi : i = s
      · subst hi
        simp only [Finsupp.single_eq_same]
        omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    have hadd := add_tsub_cancel_of_le hle
    have hd := congrArg Finsupp.degree hadd
    rw [map_add, Finsupp.degree_single, h] at hd
    have h0' : α - Finsupp.single s 1 = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
    rw [← hadd, h0', add_zero]
    simp [MvPowerSeries.coeff_X, hm, Finsupp.single_left_inj one_ne_zero]

section Solve

variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)

def ptSolveMap (x : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C :=
  fun c => ∑ b, N b c • (f b - subst (A x) (K b))

private lemma sum_smul_sum_smul_eq_of_mul_eq_one (P Q : Matrix (Fin d) (Fin d) C) (hPQ : P * Q = 1)
    (z : Fin d → MvPowerSeries τ C) (c : Fin d) : ∑ b, Q b c • ∑ a, P a b • z a = z c := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have e : ∀ a, ∑ b, Q b c * P a b = (P * Q) a c := fun a => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp_rw [e, hPQ, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem ptSolveMap_fixed_iff (hNM : N * M = 1) (hMN : M * N = 1)
    (x : Fin d → MvPowerSeries τ C) :
    ptSolveMap A K N f x = x ↔ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  constructor
  · intro hx b
    have e := sum_smul_sum_smul_eq_of_mul_eq_one N M hNM (fun c => f c - subst (A x) (K c)) b
    have hx' : ∀ a, ∑ c, N c a • (f c - subst (A x) (K c)) = x a := fun a => congrFun hx a
    simp_rw [hx'] at e
    rw [e]
    abel
  · intro h
    funext c
    have hy : ∀ b, f b - subst (A x) (K b) = ∑ a, M a b • x a := fun b => by
      rw [← h b]
      abel
    simp only [ptSolveMap]
    simp_rw [hy]
    exact sum_smul_sum_smul_eq_of_mul_eq_one M N hMN x c

variable {A K}

theorem ptSolveMap_agree
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (k : ℕ) (x y : Fin d → MvPowerSeries τ C) (hx : PTGood v x) (hy : PTGood v y)
    (hxy : PTAgree k x y) :
    PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) := by
  intro c e he
  simp only [ptSolveMap, map_sum, coeff_smul, map_sub]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pt_subst_agree (hasSubst_of_constantCoeff_zero (hA0 x hx))
    (hasSubst_of_constantCoeff_zero (hA0 y hy)) (hA0 x hx) (hA0 y hy) (K b) k
    (hAag k x y hx hy hxy) (fun α hα => (hK b α hα).imp id (fun h => h x y hx hy)) e he]

theorem ptSolveMap_good (hN : ∀ i j, N i j ∈ ptIntSub v) (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0)
    (x : Fin d → MvPowerSeries τ C) (hx : PTGood v x) :
    PTGood v (ptSolveMap A K N f x) := by
  intro c
  have hs := hasSubst_of_constantCoeff_zero (hA0 x hx)
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [ptSolveMap, map_sum, coeff_smul, map_sub, coeff_zero_eq_constantCoeff_apply,
      (hf _).1, constantCoeff_subst_eq_zero hs (hA0 x hx) (hK0 _), sub_zero, mul_zero,
      Finset.sum_const_zero]
  · exact Subring.sum_mem _ fun b _ => ptIntSer_smul (hN b c)
      (Subring.sub_mem _ (hf b).2 (ptIntSer_subst hs (hAi x hx) (hKi b)))

theorem pt_solve (hNM : N * M = 1) (hMN : M * N = 1) (hN : ∀ i j, N i j ∈ ptIntSub v)
    (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0) :
    ∃! x : Fin d → MvPowerSeries τ C,
      PTGood v x ∧ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  have hag : ∀ k (x y : Fin d → MvPowerSeries τ C), PTGood v x → PTGood v y → PTAgree k x y →
      PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) :=
    fun k x y hx hy hxy => ptSolveMap_agree (N := N) (f := f) hA0 hAag hK k x y hx hy hxy
  have hgood : ∀ x, PTGood v x → PTGood v (ptSolveMap A K N f x) :=
    fun x hx => ptSolveMap_good (N := N) (f := f) hN hf hA0 hAi hKi hK0 x hx
  have hzero : ∀ x y : Fin d → MvPowerSeries τ C, PTAgree 0 x y :=
    fun x y i e he => absurd he (Nat.not_lt_zero _)
  have hmono : ∀ k l (x y : Fin d → MvPowerSeries τ C), l ≤ k → PTAgree k x y → PTAgree l x y :=
    fun k l x y hlk h i e he => h i e (lt_of_lt_of_le he hlk)
  have htrans : ∀ k (x y z : Fin d → MvPowerSeries τ C), PTAgree k x y → PTAgree k y z →
      PTAgree k x z :=
    fun k x y z h1 h2 i e he => (h1 i e he).trans (h2 i e he)
  have hit : ∀ n, PTGood v ((ptSolveMap A K N f)^[n] 0) := by
    intro n
    induction n with
    | zero => exact ptGood_zero
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hgood _ ih
  have hstep : ∀ k, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + 1] 0) := by
    intro k
    induction k with
    | zero => exact hzero _ _
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1)]
      exact hag k _ _ (hit k) (hit (k + 1)) ih
  have hchain : ∀ k m, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + m] 0) := by
    intro k m
    induction m with
    | zero => exact fun i e he => rfl
    | succ m ih =>
      exact htrans k _ _ _ ih (hmono (k + m) k _ _ (Nat.le_add_right k m) (hstep (k + m)))
  let x : Fin d → MvPowerSeries τ C :=
    fun i e => coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i)
  have hx : ∀ n, PTAgree n x ((ptSolveMap A K N f)^[n] 0) := by
    intro n i e he
    show coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i) = _
    have hle : e.degree + 1 ≤ n := he
    have h1 := hchain (e.degree + 1) (n - (e.degree + 1))
    rw [Nat.add_sub_cancel' hle] at h1
    exact h1 i e (Nat.lt_succ_self _)
  have hxg : PTGood v x := ptGood_lim hit x hx
  have hfix : ptSolveMap A K N f x = x := by
    apply PTAgree.eq
    intro k
    cases k with
    | zero => exact hzero _ _
    | succ k =>
      have h1 : PTAgree (k + 1) (ptSolveMap A K N f x) ((ptSolveMap A K N f)^[k + 1] 0) := by
        rw [Function.iterate_succ_apply']
        exact hag k _ _ hxg (hit k) (hx k)
      exact htrans _ _ _ _ h1 (fun i e he => ((hx (k + 1)) i e he).symm)
  refine ⟨x, ⟨hxg, (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN x).mp hfix⟩, ?_⟩
  rintro y ⟨hyg, hy⟩
  have hyfix := (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN y).mpr hy
  apply PTAgree.eq
  intro k
  induction k with
  | zero => exact hzero _ _
  | succ k ih =>
    have h2 := hag k y x hyg hxg ih
    rwa [hyfix, hfix] at h2

end Solve

end

end ReciprocityTheory.ChartRestriction.G.Sh
end
