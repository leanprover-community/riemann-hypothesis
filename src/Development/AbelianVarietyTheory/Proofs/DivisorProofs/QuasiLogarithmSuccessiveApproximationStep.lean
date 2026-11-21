import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePartIntegralDifferentialOfCoboundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundaries
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LazardBinomialNormUltrametric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem symmCocycle_swap {A B : Type} [AddCommGroup A] [AddCommGroup B] (γ : A → A → B)
    (hs : ∀ x y, γ x y = γ y x) (hc : ∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0)
    (a b c e : A) :
    γ (a + b) (c + e) + γ a b + γ c e = γ (a + c) (b + e) + γ a c + γ b e := by
  have h1 := hc (a + b) c e
  have h2 := hc a b c
  have h3 := hc (a + c) b e
  have h4 := hc a c b
  rw [add_right_comm a c b] at h3
  rw [add_comm c b, hs c b] at h4
  rw [← sub_eq_zero]
  calc _ = ((γ c e - γ (a + b + c) e + γ (a + b) (c + e) - γ (a + b) c)
        - (γ b c - γ (a + b) c + γ a (b + c) - γ a b))
        - ((γ b e - γ (a + b + c) e + γ (a + c) (b + e) - γ (a + c) b)
        - (γ b c - γ (a + c) b + γ a (b + c) - γ a c)) := by abel
    _ = 0 := by rw [h1, h2, h3, h4]; simp

theorem symmCocycle_sum : ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] (γ : A → A → B), (∀ x y, γ x y = γ y x) → (∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0) → γ 0 0 = 0 → ∀ (d : ℕ) (x y : Fin d → A), γ (∑ m, x m) (∑ m, y m) = ∑ m, γ (x m) (y m) + ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) - (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) - ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) := by
  intro A B _ _ γ hs hc h0 d
  induction d with
  | zero => intro x y; simp [h0]
  | succ d ih =>
    intro x y
    have ih' := ih (fun j => x (Fin.castSucc j)) (fun j => y (Fin.castSucc j))
    simp only [Finset.sum_filter] at ih' ⊢
    simp only [Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
      if_true, lt_irrefl, if_false, add_zero] at ih' ⊢
    have hl : ∀ i : Fin d, ¬ (Fin.last d < i.castSucc) := fun i => not_lt.mpr (Fin.castSucc_lt_last i).le
    simp only [hl, if_false, add_zero] at ih' ⊢
    have k := symmCocycle_swap γ hs hc (∑ m : Fin d, x m.castSucc) (x (Fin.last d)) (∑ m : Fin d, y m.castSucc) (y (Fin.last d))
    rw [ih'] at k
    rw [Finset.sum_add_distrib]
    rw [← sub_eq_zero] at k ⊢
    rw [← k]
    abel

end GlobalTheory
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmCocycle_apply_finset_sum : ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] (γ : A → A → B), (∀ x y, γ x y = γ y x) → (∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0) → γ 0 0 = 0 → ∀ (d : ℕ) (x y : Fin d → A), γ (∑ m, x m) (∑ m, y m) = ∑ m, γ (x m) (y m) + ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) - (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) - ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) := by
  atlas_forward_decl GlobalTheory.symmCocycle_sum
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zeroPt {σ τ : Type} [Finite σ] (f : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) f = C (constantCoeff f) := by
  classical
  have hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · rw [Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff_apply, coeff_C, coeff_one, smul_eq_mul]
    split_ifs <;> simp
  · intro dd hdd
    obtain ⟨s, hs'⟩ := Finsupp.ne_iff.1 hdd
    have hmem : s ∈ dd.support := Finsupp.mem_support_iff.2 (by simpa using hs')
    rw [Finsupp.prod, Finset.prod_eq_zero hmem (zero_pow (Finsupp.mem_support_iff.1 hmem)), map_zero,
      smul_zero]

theorem hs2 {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hs2 hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl


theorem op_addLaw {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : op (addLaw R d) u v = u + v := by
  funext i
  unfold op addLaw at2
  rw [subst_add (hs2 hu hv), subst_X (hs2 hu hv), subst_X (hs2 hu hv)]
  rfl

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem coc_at {τ : Type} [Finite τ] {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : cob2 (addLaw R d) c = 0) {u v w : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    at2 c v w - at2 c (u + v) w + at2 c u (v + w) - at2 c u v = 0 := by
  set a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w) with ha_def
  have ha0 : ∀ t, constantCoeff (a t) = 0 := fun t => by
    rcases t with t | t | t <;> simp [a, hu, hv, hw]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x1]
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x2]
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x3]
  have e1 : (fun i => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = u := by
    funext i; simp only [x1]; rw [subst_X ha]; rfl
  have e2 : (fun i => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = v := by
    funext i; simp only [x2]; rw [subst_X ha]; rfl
  have e3 : (fun i => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = w := by
    funext i; simp only [x3]; rw [subst_X ha]; rfl
  have hadd : ∀ p q : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R,
      (fun i => subst a ((p + q) i)) = (fun i => subst a (p i)) + (fun i => subst a (q i)) := by
    intro p q; funext i; simp only [Pi.add_apply]; rw [subst_add ha]
  have h12 : ∀ i, constantCoeff ((x1 + x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h1, h2]
  have h23 : ∀ i, constantCoeff ((x2 + x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h2, h3]
  have key := congrArg (subst a) hc
  unfold cob2 at key
  rw [op_addLaw h1 h2, op_addLaw h2 h3] at key
  rw [subst_sub ha, subst_add ha, subst_sub ha, subst_powerSeriesEvalTwoGroups h2 h3 ha0, subst_powerSeriesEvalTwoGroups h12 h3 ha0,
    subst_powerSeriesEvalTwoGroups h1 h23 ha0, subst_powerSeriesEvalTwoGroups h1 h2 ha0, hadd, hadd, e1, e2, e3] at key
  rw [key, ← coe_substAlgHom ha, map_zero]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

variable (R d) in

def PtGrp (τ : Type) : AddSubgroup (Fin d → MvPowerSeries τ R) where
  carrier := {u | ∀ i, constantCoeff (u i) = 0}
  zero_mem' := fun i => by simp
  add_mem' := fun {u v} hu hv i => by simp [hu i, hv i]
  neg_mem' := fun {u} hu i => by simp [hu i]

theorem sum_single_apply {M : Type} [AddCommMonoid M] (s : Finset (Fin d)) (w : Fin d → M) (i : Fin d) :
    (∑ j ∈ s, Pi.single j (w j) : Fin d → M) i = if i ∈ s then w i else 0 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq]

theorem subst_sum_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (s : Finset (Fin d)) :
    (fun i => subst a ((∑ j ∈ s, Pi.single j (X j) : Fin d → MvPowerSeries (Fin d) R) i)) =
      ∑ j ∈ s, Pi.single j (a j) := by
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [sum_single_apply, sum_single_apply]
  split_ifs
  · exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]

theorem cc_sum_single {τ : Type} (s : Finset (Fin d)) (w : Fin d → MvPowerSeries τ R)
    (hw : ∀ j, constantCoeff (w j) = 0) (i : Fin d) :
    constantCoeff ((∑ j ∈ s, Pi.single j (w j) : Fin d → MvPowerSeries τ R) i) = 0 := by
  rw [sum_single_apply]; split_ifs <;> simp [hw]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (m : Fin d) :
    (fun i => subst a ((Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R) i)) = Pi.single m (a m) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h; exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]

variable (R) in

def corr (c : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (X j))
    (Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R)

theorem subst_corr {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (corr R c) = ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (a j))
      (Pi.single m (a m)) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  unfold corr
  rw [← coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coe_substAlgHom hS, subst_powerSeriesEvalTwoGroups (cc_sum_single _ _ (fun j => by simp))
    (fun i => by rw [Pi.single_apply]; split_ifs <;> simp) ha, subst_sum_single ha, subst_single ha]

end GlobalTheory.SymCocAdd

namespace GlobalTheory

open GlobalTheory.SymCocAdd in

theorem symmetricCocycle_additive_eq_coboundary_add_alt (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : IsCoc (addLaw R d) c) (h0 : constantCoeff c = 0) :
    ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b +
      ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (Pi.single m (X (Sum.inr m))) := by
  classical
  let τ := Fin d ⊕ Fin d
  let A := PtGrp R d τ
  let γ : A → A → MvPowerSeries τ R := fun u v => at2 c u.1 v.1
  have hsymm : ∀ u v, γ u v = γ v u := by
    intro u v
    have hX1 : ∀ i, constantCoeff ((fun i => (X (Sum.inr i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have hX2 : ∀ i, constantCoeff ((fun i => (X (Sum.inl i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have huv : ∀ t, constantCoeff (Sum.elim u.1 v.1 t) = 0 := fun t => by
      cases t with
      | inl t => exact u.2 t
      | inr t => exact v.2 t
    have := subst_powerSeriesEvalTwoGroups hX1 hX2 huv c
    change at2 (swap c) u.1 v.1 = _ at this
    rw [hc.2] at this
    simp only [γ]
    rw [this]
    have hS : HasSubst (Sum.elim u.1 v.1) := hasSubst_of_constantCoeff_zero huv
    congr 1 <;> funext i <;> rw [subst_X hS] <;> rfl
  have hcoc : ∀ x y z : A, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0 :=
    fun x y z => coc_at hc.1 x.2 y.2 z.2
  have hzero : γ 0 0 = 0 := by
    simp only [γ]
    unfold at2
    have : Sum.elim ((0 : A) : Fin d → MvPowerSeries τ R) ((0 : A) : Fin d → MvPowerSeries τ R) =
        fun _ => 0 := by funext t; cases t <;> rfl
    rw [this, subst_zeroPt, h0, map_zero]
  let x : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inl m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  let y : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inr m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  have key := GlobalTheory.T.symmCocycle_apply_finset_sum A (MvPowerSeries τ R) γ hsymm hcoc hzero d x y
  have coeA : ∀ (s : Finset (Fin d)) (f : Fin d → A),
      ((∑ j ∈ s, f j : A) : Fin d → MvPowerSeries τ R) = ∑ j ∈ s, (f j : Fin d → MvPowerSeries τ R) :=
    fun s f => map_sum A.subtype f s
  have hL : γ (∑ m, x m) (∑ m, y m) = c := by
    simp only [γ]
    rw [coeA, coeA]
    simp only [x, y]
    rw [Finset.univ_sum_single (fun m => (X (Sum.inl m) : MvPowerSeries τ R)),
      Finset.univ_sum_single (fun m => (X (Sum.inr m) : MvPowerSeries τ R))]
    unfold at2
    have : Sum.elim (fun m => (X (Sum.inl m) : MvPowerSeries τ R)) (fun m => X (Sum.inr m)) = X := by
      funext t; cases t <;> rfl
    rw [this, subst_self]; rfl
  have hT : ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) -
      (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) -
      ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) = cob1 (addLaw R d) (corr R c) := by
    unfold cob1 inL inR
    rw [subst_corr (fun i => by simp [addLaw]), subst_corr (fun i => by simp),
      subst_corr (fun i => by simp)]
    simp only [γ, coeA]
    simp only [x, y, AddSubgroup.coe_add, ← Pi.single_add]
    rfl
  refine ⟨corr R c, ?_⟩
  calc c = γ (∑ m, x m) (∑ m, y m) := hL.symm
    _ = _ := key
    _ = _ := by rw [hT, add_comm]

end GlobalTheory
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), IsCoc (addLaw R d) c → constantCoeff c = 0 → ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b + ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m))) := by
  atlas_forward_decl GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.LazardOne

theorem choose_pow_mul_add_modEq_one (p : ℕ) [hp : Fact p.Prime] :
    ∀ (s A B : ℕ), B < p ^ s → (p ^ s * A + B).choose B ≡ 1 [MOD p] := by
  intro s
  induction s with
  | zero =>
    intro A B hB
    have : B = 0 := by simpa using hB
    subst this
    simp [Nat.ModEq]
  | succ s ih =>
    intro A B hB
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _
    have e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A) := by ring
    rw [e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self,
      one_mul] at h
    have hB' : B / p < p ^ s := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]; exact hB
    have := ih A (B / p) hB'
    rw [add_comm (p ^ s * A)] at this
    rw [e0]; exact h.trans this

theorem not_dvd_choose_pow_mul_add (p : ℕ) [hp : Fact p.Prime] (s A B : ℕ) (hB : B < p ^ s) :
    ¬ p ∣ (p ^ s * A + B).choose B := by
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans (choose_pow_mul_add_modEq_one p s A B hB)
  exact hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.1 h0.symm)

variable (p : ℕ) [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem eq_zero_of_eq_zero (N : ℕ) (c : ℕ → k)
    (hsym : ∀ i, i ≤ N → c i = c (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      c (i + j) * ((i + j).choose i : k) = c i * ((j + l).choose j : k))
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (h0 : c (p ^ s) = 0) : ∀ n, 0 < n → n < N → c n = 0 := by
  have hA : ∀ i n, c i = 0 → 0 < i → i < n → n < N → ¬ p ∣ n.choose i → c n = 0 := by
    intro i n hi hi0 hin hnN hd
    have h := hrel i (n - i) (N - n) hi0 (by omega) (by omega) (by omega)
    rw [show i + (n - i) = n by omega, hi, zero_mul] at h
    have hne : ((n.choose i : ℕ) : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k p]; exact hd
    exact (mul_eq_zero.1 h).resolve_right hne
  have hq : 0 < p ^ s := pow_pos hp.out.pos s
  have hb1 : ∀ u, 0 < u → u < K → ¬ p ∣ u → c (p ^ s * u) = 0 := by
    intro u hu huK hpu
    rcases Nat.lt_or_ge 1 u with h1 | h1
    · refine hA (p ^ s) (p ^ s * u) h0 hq (lt_mul_of_one_lt_right hq h1) ?_
        (GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp.out u hpu s)
      rw [hN]; exact Nat.mul_lt_mul_of_pos_left huK hq
    · have : u = 1 := by omega
      subst this; simpa using h0
  have hb : ∀ u, 0 < u → u < K → c (p ^ s * u) = 0 := by
    intro u hu huK
    rcases hK u hu huK with h | h
    · exact hb1 u hu huK h
    · have h' := hb1 (K - u) (by omega) (by omega) h
      have hle : p ^ s * (K - u) ≤ N := by rw [hN]; exact Nat.mul_le_mul_left _ (by omega)
      rw [hsym _ hle] at h'
      rwa [show N - p ^ s * (K - u) = p ^ s * u by
        rw [hN, ← Nat.mul_sub]; congr 1; omega] at h'
  intro n hn hnN
  obtain ⟨u, v, hvlt, rfl⟩ : ∃ u v, v < p ^ s ∧ n = p ^ s * u + v :=
    ⟨n / p ^ s, n % p ^ s, Nat.mod_lt _ hq, (Nat.div_add_mod n (p ^ s)).symm⟩
  have huK : u < K := by
    apply Nat.lt_of_mul_lt_mul_left (a := p ^ s)
    rw [← hN]; omega
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv
    rw [add_zero] at hn ⊢
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simp at hn
    · exact hb u hu huK
  · have hK1 : c (p ^ s * (K - 1)) = 0 := hb (K - 1) (by omega) (by omega)
    have e1 : p ^ s * K = p ^ s * (K - 1) + p ^ s := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hNv : N - v = p ^ s * (K - 1) + (p ^ s - v) := by omega
    have hpos : 0 < p ^ s * (K - 1) := Nat.mul_pos hq (by omega)
    have hcNv : c (N - v) = 0 := by
      rw [hNv]
      refine hA (p ^ s * (K - 1)) _ hK1 hpos (by omega) (by omega) ?_
      rw [Nat.choose_symm_add]
      exact not_dvd_choose_pow_mul_add p s (K - 1) (p ^ s - v) (by omega)
    have hcv : c v = 0 := by rw [hsym v (by omega), hcNv]
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simpa using hcv
    · have hsu : 0 < p ^ s * u := Nat.mul_pos hq hu
      exact hA v _ hcv hv (by omega) hnN (not_dvd_choose_pow_mul_add p s u v hvlt)

theorem exists_scalar (N : ℕ) (a : ℕ → k)
    (hsym : ∀ i, i ≤ N → a i = a (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k))
    (g : ℕ) (hg : 0 < g) (hdiv : ∀ i, 0 < i → i < N → g ∣ N.choose i)
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (hb : ((N.choose (p ^ s) / g : ℕ) : k) ≠ 0) :
    ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
  set b : ℕ → k := fun i => ((N.choose i / g : ℕ) : k) with hbdef
  have hbsym : ∀ i, i ≤ N → b (N - i) = b i := by
    intro i hi; simp only [hbdef, Nat.choose_symm hi]
  have hbrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      b (i + j) * ((i + j).choose i : k) = b i * ((j + l).choose j : k) := by
    intro i j l hi hj hl hs
    obtain ⟨x, hx⟩ := hdiv (i + j) (by omega) (by omega)
    obtain ⟨y, hy⟩ := hdiv i hi (by omega)
    have hm := Nat.choose_mul (n := N) (k := i + j) (s := i) (by omega)
    rw [show N - i = j + l by omega, show i + j - i = j by omega, hx, hy, mul_assoc, mul_assoc] at hm
    have hm' := Nat.eq_of_mul_eq_mul_left hg hm
    simp only [hbdef, hx, hy, Nat.mul_div_cancel_left _ hg]
    rw [← Nat.cast_mul, ← Nat.cast_mul, hm']
  refine ⟨a (p ^ s) / b (p ^ s), ?_⟩
  have key := eq_zero_of_eq_zero p N (fun i => a i - a (p ^ s) / b (p ^ s) * b i) ?_ ?_ s K hN hK2 hK ?_
  · intro i hi hiN
    exact sub_eq_zero.1 (key i hi hiN)
  · intro i hi
    rw [hsym i hi, hbsym i hi]
  · intro i j l hi hj hl hs
    rw [sub_mul, sub_mul, hrel i j l hi hj hl hs, mul_assoc, mul_assoc, hbrel i j l hi hj hl hs]
  · rw [div_mul_cancel₀ _ hb, sub_self]

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ)
    (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) →
    (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) →
    ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k,
      t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧
      WittVector.constantCoeff w = a i := by
  intro p _ k _ _ _ N a hN2 hsym hrel
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg, hg1, hdiv, z, hz⟩ : ∃ g, 0 < g ∧ (g = 1 ∨ g = p) ∧
      (∀ i, 0 < i → i < N → g ∣ N.choose i) ∧
      ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
    obtain ⟨r, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) p hp.one_lt.ne'
    by_cases hm1 : m = 1
    · subst hm1
      rw [mul_one] at hNe
      have hr : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · subst h; simp at hNe; omega
        · exact h
      have hdv : ∀ i, 0 < i → i < N → p ∣ N.choose i := by
        intro i hi hiN; rw [hNe] at hiN ⊢; exact hp.dvd_choose_pow (by omega) (by omega)
      refine ⟨p, hp.pos, Or.inr rfl, hdv, ?_⟩
      obtain ⟨c, hc, hch⟩ := GlobalTheory.Honda.Lazard.choose_prime_pow_pred hp r hr
      refine exists_scalar p N a hsym hrel p hp.pos hdv (r - 1) p ?_ hp.two_le ?_ ?_
      · rw [hNe, ← pow_succ]; congr 1; omega
      · intro u hu hup; left; exact fun h => absurd (Nat.le_of_dvd hu h) (by omega)
      · rw [hNe, hch, Nat.mul_div_cancel_left _ hp.pos, Ne, CharP.cast_eq_zero_iff k p]; exact hc
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hNe; omega
      have hm2 : 2 ≤ m := by omega
      refine ⟨1, one_pos, Or.inl rfl, fun _ _ _ => one_dvd _, ?_⟩
      refine exists_scalar p N a hsym hrel 1 one_pos (fun _ _ _ => one_dvd _) r m hNe hm2 ?_ ?_
      · intro u hu huK
        by_contra h
        push_neg at h
        have := Nat.dvd_add h.2 h.1
        rw [Nat.sub_add_cancel huK.le] at this
        exact hm this
      · rw [Nat.div_one, hNe, Ne, CharP.cast_eq_zero_iff k p]
        exact GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp m hm r
  have hgW : ((g : ℕ) : WittVector p k) ≠ 0 := by
    rcases hg1 with h | h
    · subst h; simp
    · rw [h]
      intro h0
      have := congrArg (fun x : WittVector p k => x.coeff 1) h0
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
      exact one_ne_zero this
  have hgF : ((g : ℕ) : Fr p k) ≠ 0 := by
    rw [← map_natCast (algebraMap (WittVector p k) (Fr p k)), Ne,
      map_eq_zero_iff _ (IsFractionRing.injective (WittVector p k) (Fr p k))]
    exact hgW
  refine ⟨algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p z) / (g : Fr p k), ?_⟩
  intro i hi hiN
  obtain ⟨q, hq⟩ := hdiv i hi hiN
  refine ⟨WittVector.teichmuller p z * (q : WittVector p k), ?_, ?_⟩
  · rw [hq, Nat.cast_mul, map_mul, map_natCast]
    field_simp
  · rw [hz i hi hiN, hq, Nat.mul_div_cancel_left _ hg, map_mul, map_natCast,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

end GlobalTheory.LazardOne
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lazard_one_variable_exists_witt_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ) (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) → (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) → ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k, t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧ WittVector.constantCoeff w = a i := by
  atlas_forward_decl GlobalTheory.LazardOne.exists_lift
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m)))) = if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) + Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  first | exact @GlobalTheory.coeff_at2_single_X_inl_inr | exact GlobalTheory.coeff_at2_single_X_inl_inr | (intros; apply GlobalTheory.coeff_at2_single_X_inl_inr <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.CocRel

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

abbrev ex3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single (0 : Fin 3) a + Finsupp.single 1 b + Finsupp.single 2 c

theorem threeVariableMonomialExponent_eq_iff (a b c a' b' c' : ℕ) : ex3 a b c = ex3 a' b' c' ↔ a' = a ∧ b' = b ∧ c' = c := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    have h2 := DFunLike.congr_fun h 2
    simp at h0 h1 h2
    exact ⟨h0.symm, h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem coeff_mono3 (a b c i j l : ℕ) (r : ℕ) :
    coeff (R := R) (ex3 i j l) (X 0 ^ a * X 1 ^ b * X 2 ^ c * (r : MvPowerSeries (Fin 3) R)) =
      if a = i ∧ b = j ∧ c = l then (r : R) else 0 := by
  rw [← map_natCast (C : R →+* MvPowerSeries (Fin 3) R), coeff_mul_C, X_pow_eq, X_pow_eq, X_pow_eq,
    monomial_mul_monomial, monomial_mul_monomial, coeff_monomial]
  have := threeVariableMonomialExponent_eq_iff i j l a b c
  by_cases h : a = i ∧ b = j ∧ c = l
  · rw [if_pos (this.2 h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, zero_mul]

theorem coeff_left (p q i j l : ℕ) :
    coeff (ex3 i j l) ((X 0 + X 1) ^ p * X 2 ^ q : MvPowerSeries (Fin 3) R) =
      if p = i + j ∧ q = l then (p.choose i : R) else 0 := by
  rw [add_pow, Finset.sum_mul, map_sum]
  simp only [mul_right_comm _ (_ : MvPowerSeries (Fin 3) R) (X 2 ^ q)]
  have h : ∀ k, coeff (R := R) (ex3 i j l) (X 0 ^ k * X 2 ^ q * X 1 ^ (p - k) * ((p.choose k : ℕ) :
      MvPowerSeries (Fin 3) R)) = if k = i ∧ p - k = j ∧ q = l then (p.choose k : R) else 0 := by
    intro k
    rw [← coeff_mono3, mul_right_comm (X 0 ^ k)]
  simp only [h]
  rw [Finset.sum_eq_single i]
  · by_cases hp : i ≤ p
    · exact if_congr (by omega) rfl rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro k _ hk
    exact if_neg fun h' => hk h'.1
  · intro hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]; simp

theorem coeff_right (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 0 ^ p * (X 1 + X 2) ^ q : MvPowerSeries (Fin 3) R) =
      if p = i ∧ q = j + l then (q.choose j : R) else 0 := by
  rw [add_pow, Finset.mul_sum, map_sum]
  simp only [← mul_assoc, coeff_mono3]
  rw [Finset.sum_eq_single j]
  · by_cases hp : j ≤ q
    · exact if_congr (by omega) rfl rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro k _ hk
    exact if_neg fun h' => hk h'.2.1
  · intro hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]; simp

theorem coeff_yz (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 1 ^ p * X 2 ^ q : MvPowerSeries (Fin 3) R) =
      if 0 = i ∧ p = j ∧ q = l then 1 else 0 := by
  simpa using coeff_mono3 (R := R) 0 p q i j l 1

theorem coeff_xy (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 0 ^ p * X 1 ^ q : MvPowerSeries (Fin 3) R) =
      if p = i ∧ q = j ∧ 0 = l then 1 else 0 := by
  simpa using coeff_mono3 (R := R) p q 0 i j l 1

theorem coeff_powerSeriesEvalTwoGroups_piSingle (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d)
    {A B : MvPowerSeries τ R} (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (e : τ →₀ ℕ) (p q : ℕ) (h : ∀ p' q', ¬ (p' = p ∧ q' = q) → coeff e (A ^ p' * B ^ q') = 0) :
    coeff e (at2 c (Pi.single m A) (Pi.single m B)) =
      coeff (Finsupp.single (Sum.inl m) p + Finsupp.single (Sum.inr m) q) c *
        coeff e (A ^ p * B ^ q) := by
  have h0 : ∀ {A : MvPowerSeries τ R}, constantCoeff A = 0 → ∀ i,
      constantCoeff ((Pi.single m A : Fin d → MvPowerSeries τ R) i) = 0 := by
    intro A hA i
    by_cases hi : i = m
    · subst hi; simpa using hA
    · simp [hi]
  have hs := SubstCalc.hasSubst_elim (h0 hA) (h0 hB)
  have hprod : ∀ p' q', (Finsupp.single (Sum.inl m) p' + Finsupp.single (Sum.inr m) q' :
      Fin d ⊕ Fin d →₀ ℕ).prod (fun s k => (Sum.elim (Pi.single m A) (Pi.single m B) s :
        MvPowerSeries τ R) ^ k) = A ^ p' * B ^ q' := by
    intro p' q'
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by exact pow_zero _),
      Finsupp.prod_single_index (by exact pow_zero _)]
    simp
  unfold at2
  rw [coeff_subst hs,
    finsum_eq_single _ (Finsupp.single (Sum.inl m) p + Finsupp.single (Sum.inr m) q), hprod,
    smul_eq_mul]
  intro δ hδ
  by_cases hc : δ = Finsupp.single (Sum.inl m) (δ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (δ (Sum.inr m))
  · rw [congrArg (fun δ' : Fin d ⊕ Fin d →₀ ℕ => δ'.prod _) hc, hprod, h, smul_zero]
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hc
    exact hδ hc
  · obtain ⟨s, hs'⟩ : ∃ s, δ s ≠ (Finsupp.single (Sum.inl m) (δ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (δ (Sum.inr m)) : Fin d ⊕ Fin d →₀ ℕ) s := by
      by_contra hh
      exact hc (Finsupp.ext fun s => by_contra fun h' => hh ⟨s, h'⟩)
    have key : δ s ≠ 0 ∧ (Sum.elim (Pi.single m A) (Pi.single m B) s : MvPowerSeries τ R) = 0 := by
      rcases s with t | t <;> by_cases ht : t = m
      · subst ht; simp at hs'
      · simpa [ht, Finsupp.single_apply, Ne.symm ht] using hs'
      · subst ht; simp at hs'
      · simpa [ht, Finsupp.single_apply, Ne.symm ht] using hs'
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 key.1)
      (by rw [key.2, zero_pow key.1]), map_zero, smul_zero]

theorem cocycle_at (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : cob2 (addLaw R d) c = 0)
    {u v t : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (ht : ∀ i, constantCoeff (t i) = 0) :
    at2 c v t - at2 c (u + v) t + at2 c u (v + t) - at2 c u v = 0 := by
  set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v t) with hw
  have hw0 : ∀ s, constantCoeff (w s) = 0 := fun s => by
    rcases s with s | s | s <;> simp [hw, hu, hv, ht]
  have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
  have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
    unfold x1; rw [subst_X hsw]; rfl
  have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = v i := fun i => by
    unfold x2; rw [subst_X hsw]; rfl
  have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = t i := fun i => by
    unfold x3; rw [subst_X hsw]; rfl
  have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      op (addLaw R d) a b = a + b := by
    intro a b ha hb
    funext i
    unfold op addLaw at2
    have := SubstCalc.hasSubst_elim ha hb
    rw [subst_add this, subst_X this, subst_X this]
    rfl
  have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff ((a + b) i) = 0 := by
    intro a b ha hb i; simp [ha, hb]
  have key := congrArg (subst w) hc
  unfold cob2 at key
  rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
  rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
    SubstCalc.subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, SubstCalc.subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
    SubstCalc.subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, SubstCalc.subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
  have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
    intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
  rw [e, e] at key
  simp only [h1, h2, h3] at key
  have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
    simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
  rw [e0] at key
  convert key using 2

theorem relations : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), cob2 (addLaw R d) c = 0 → ∀ m : Fin d, (∀ n, 0 < n → coeff (Finsupp.single (Sum.inl m) n) c = 0) ∧ ∀ i j l, 0 < i → 0 < j → 0 < l → coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c * ((i + j).choose i : R) = coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c * ((j + l).choose j : R) := by
  intro R _ d c hc m
  have h0 : ∀ (k : Fin 3) i,
      constantCoeff ((Pi.single m (X k) : Fin d → MvPowerSeries (Fin 3) R) i) = 0 := by
    intro k i
    by_cases hi : i = m
    · subst hi; simp
    · simp [hi]
  have hid := cocycle_at c hc (h0 0) (h0 1) (h0 2)
  rw [← Pi.single_add, ← Pi.single_add] at hid
  have key : ∀ i j l : ℕ, 0 < i →
      - coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c *
        ((i + j).choose i : R) +
      coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c *
        ((j + l).choose j : R) -
      coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j) c *
        (if 0 = l then 1 else 0) = 0 := by
    intro i j l hi
    have h := congrArg (coeff (ex3 i j l)) hid
    rw [map_sub, map_add, map_sub, map_zero,
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ j l
        (fun p q hpq => by rw [coeff_yz, if_neg (by omega)]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ (i + j) l
        (fun p q hpq => by rw [coeff_left, if_neg hpq]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ i (j + l)
        (fun p q hpq => by rw [coeff_right, if_neg hpq]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ i j
        (fun p q hpq => by rw [coeff_xy, if_neg (by omega)]),
      coeff_yz, coeff_left, coeff_right, coeff_xy, if_neg (by omega), if_pos ⟨rfl, rfl⟩,
      if_pos ⟨rfl, rfl⟩] at h
    simp only [true_and] at h
    linear_combination h
  refine ⟨fun n hn => ?_, fun i j l hi _ hl => ?_⟩
  · simpa using key n 0 0 hn
  · have h := key i j l hi
    rw [if_neg (by omega)] at h
    linear_combination -h

end GlobalTheory.Katz.CocRel
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), cob2 (addLaw R d) c = 0 → ∀ m : Fin d, (∀ n, 0 < n → coeff (Finsupp.single (Sum.inl m) n) c = 0) ∧ ∀ i j l, 0 < i → 0 < j → 0 < l → coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c * ((i + j).choose i : R) = coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c * ((j + l).choose j : R) := by
  atlas_forward_decl GlobalTheory.Katz.CocRel.relations
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem coboundaryOne_additiveFormalGroupLaw_X_pow (R : Type) [CommRing R] (d N : ℕ) (m : Fin d) (hN : 1 ≤ N) :
    cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N,
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
  have h1 : HasSubst (addLaw R d) := hasSubst_of_constantCoeff_zero fun i => by simp [addLaw]
  have h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold cob1 inL inR
  rw [subst_pow h1, subst_pow h2, subst_pow h3, subst_X h1, subst_X h2, subst_X h3]
  simp only [addLaw]
  have hr : Finset.range (N + 1) = insert 0 (insert N (Finset.Ioo 0 N)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [add_pow, hr, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
  simp only [pow_zero, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, mul_one, one_mul]
  have key : ∀ i ∈ Finset.Ioo 0 N,
      (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R) ^ i * X (Sum.inr m) ^ (N - i) *
        (N.choose i : MvPowerSeries (Fin d ⊕ Fin d) R) =
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
    intro i _
    rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, ← nsmul_eq_mul', ← map_nsmul,
      nsmul_one]
  rw [Finset.sum_congr rfl key]
  abel

end GlobalTheory
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose : ∀ (R : Type) [CommRing R] (d N : ℕ) (m : Fin d), 1 ≤ N → cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N, monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i)) (N.choose i : R) := by
  atlas_forward_decl GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

private theorem homog_one {R τ : Type} [CommRing R] : (1 : MvPowerSeries τ R).IsHomogeneous 0 := by
  classical
  intro γ h
  rw [coeff_one] at h
  by_cases h0 : γ = 0
  · simp [h0]
  · simp [h0] at h

private theorem homog_X {R τ : Type} [CommRing R] (t : τ) :
    (X t : MvPowerSeries τ R).IsHomogeneous 1 := by
  classical
  intro γ h
  rw [coeff_X] at h
  by_cases h0 : γ = Finsupp.single t 1
  · simp [h0, Finsupp.weight_single]
  · simp [h0] at h

private theorem homog_pow {R τ : Type} [CommRing R] {f : MvPowerSeries τ R}
    (hf : f.IsHomogeneous 1) (n : ℕ) : (f ^ n).IsHomogeneous n := by
  induction n with
  | zero => rw [pow_zero]; exact homog_one
  | succ n ih => rw [pow_succ]; exact IsHomogeneous.mul (f := f ^ n) (g := f) ih hf

private theorem homog_prod {R σ τ : Type} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, (a i).IsHomogeneous 1) (n : σ → ℕ) (s : Finset σ) :
    (∏ i ∈ s, a i ^ n i).IsHomogeneous (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact homog_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]; exact IsHomogeneous.mul (f := a i ^ n i) (p := n i) (homog_pow (ha i) (n i)) ih

theorem coeff_subst_linear_eq_zero_of_degree {R σ τ : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, (a i).IsHomogeneous 1) {N : ℕ}
    {b : MvPowerSeries σ R} (hb : ∀ α : σ →₀ ℕ, α.degree = N → coeff α b = 0)
    {γ : τ →₀ ℕ} (hγ : γ.degree = N) : coeff γ (subst a b) = 0 := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact IsHomogeneous.coeff_eq_zero (f := a i) (p := 1) (ha i) (by simp)
  rw [coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree = N
  · rw [hb α h, zero_smul]
  · have := IsHomogeneous.coeff_eq_zero (f := ∏ i ∈ α.support, a i ^ α i)
      (p := ∑ i ∈ α.support, α i) (homog_prod ha α α.support) (d := γ) (by
      rw [hγ]; exact fun h' => h h'.symm)
    rw [Finsupp.prod, this, smul_zero]

theorem coeff_cob1_addLaw_eq_zero_of_degree_eq : ∀ (R : Type) [CommRing R] (d N : ℕ)
    (b : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree = N → coeff α b = 0) →
    ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → coeff γ (cob1 (addLaw R d) b) = 0 := by
  intro R _ d N b hb γ hγ
  unfold cob1 inL inR
  rw [map_sub, map_sub,
    coeff_subst_linear_eq_zero_of_degree (a := addLaw R d)
      (fun i => IsHomogeneous.add (p := 1) (homog_X (Sum.inl i)) (homog_X (Sum.inr i))) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ]
  simp

end GlobalTheory.Katz
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coboundaryOne_additive_eq_zero_of_degree : ∀ (R : Type) [CommRing R] (d N : ℕ) (b : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree = N → coeff α b = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → coeff γ (cob1 (addLaw R d) b) = 0 := by
  atlas_forward_decl GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option maxHeartbeats 800000

namespace GlobalTheory.LazardHomog

theorem lift_addLaw (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext α
  rw [coeff_lift]
  simp only [addLaw, map_add, coeff_X]
  have hne : (Finsupp.single (Sum.inl i) 1 : Fin d ⊕ Fin d →₀ ℕ) ≠ Finsupp.single (Sum.inr i) 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]; simp
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · simp [h1, hne]
  · by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · simp [h2, hne.symm]
    · simp [h1, h2]

theorem homogCoc_red_cob : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) k), 2 ≤ N → IsCoc (addLaw k d) c → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ Red p (cob1 (addLaw (Fr p k) d) h) c := by
  intro p _ k _ _ _ d N c hN hc hhom
  have hconst : ∀ (R : Type) [CommRing R] (i : Fin d), constantCoeff (addLaw R d i) = 0 := by
    intro R _ i; simp [addLaw]
  have hc0 : constantCoeff c = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hhom 0 (by simp; omega)
  obtain ⟨b, hb⟩ := GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add k d c hc hc0
  set cm : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k := fun m => at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (Pi.single m (X (Sum.inr m))) with hcm
  set bN := homogeneousComponent N b with hbN
  have hbNc : ∀ α, coeff α bN = if α.degree = N then coeff α b else 0 := fun α =>
    coeff_homogeneousComponent N α b

  have hdec : c = cob1 (addLaw k d) bN + ∑ m, cm m := by
    ext γ
    by_cases hγ : γ.degree = N
    · have e1 : coeff γ (cob1 (addLaw k d) b) = coeff γ (cob1 (addLaw k d) bN) := by
        have := formalCoboundary_add (hconst k) bN (b - bN)
        rw [add_sub_cancel] at this
        rw [this, map_add, GlobalTheory.T.coeff_coboundaryOne_additive_eq_zero_of_degree k d N (b - bN) (fun α hα => by
          rw [map_sub, hbNc, if_pos hα, sub_self]) γ hγ, add_zero]
      conv_lhs => rw [hb]
      rw [map_add, map_add, e1]
    · rw [hhom γ hγ, map_add, map_sum, (GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).1 bN (fun α hα => by
        rw [hbNc, if_neg hα]) γ hγ, zero_add]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      simp only [cm]
      rw [GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair]
      split_ifs <;> simp [hhom γ hγ]

  set a : Fin d → ℕ → k := fun m n => coeff (Finsupp.single (Sum.inl m) n + Finsupp.single (Sum.inr m) (N - n)) c with ha
  have hsym : ∀ m n, n ≤ N → a m n = a m (N - n) := by
    intro m n hn
    simp only [ha]
    conv_lhs => rw [← hc.2]
    rw [(GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).2.2.1, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Nat.sub_sub_self hn, add_comm]
    rfl
  have hrel : ∀ m i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a m (i + j) * ((i + j).choose i : k) = a m i * ((j + l).choose j : k) := by
    intro m i j l hi hj hl hs
    simp only [ha]
    have e1 : N - (i + j) = l := by omega
    have e2 : N - i = j + l := by omega
    rw [e1, e2]
    exact (GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).2 i j l hi hj hl
  have ht := fun m => GlobalTheory.T.lazard_one_variable_exists_witt_lift p k N (a m) hN (hsym m) (hrel m)
  choose t ht using ht
  have hzero : ∀ m, coeff (Finsupp.single (Sum.inl m) N) c = 0 :=
    fun m => (GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).1 N (by omega)
  have hzero' : ∀ m, coeff (Finsupp.single (Sum.inr m) N) c = 0 := by
    intro m
    have := hsym m 0 (Nat.zero_le _)
    simp only [ha, Finsupp.single_zero, zero_add, Nat.sub_zero, Nat.sub_self, add_zero] at this
    rw [this, hzero]
  have hconstFr := hconst (Fr p k)
  have redSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
      (G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ m ∈ s, Red p (F m) (G m)) →
      Red p (∑ m ∈ s, F m) (∑ m ∈ s, G m) := by
    intro s F G hFG
    induction s using Finset.induction_on with
    | empty => intro α; exact ⟨0, by simp⟩
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ (hFG x (Finset.mem_insert_self _ _))
        (ih fun m hm => hFG m (Finset.mem_insert_of_mem hm))).1
  have cob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconstFr (0 : Fr p k) 0
    simpa using this
  have cobSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d) (Fr p k)),
      cob1 (addLaw (Fr p k) d) (∑ m ∈ s, F m) = ∑ m ∈ s, cob1 (addLaw (Fr p k) d) (F m) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simpa using cob0
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, formalCoboundary_add hconstFr, ih]
  have redm : ∀ m, Red p (t m • cob1 (addLaw (Fr p k) d) (X m ^ N)) (cm m) := by
    intro m α
    rw [GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose (Fr p k) d N m (by omega)]
    simp only [cm]
    rw [GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair, map_smul, map_sum]
    simp only [coeff_monomial, smul_eq_mul]
    set i := α (Sum.inl m) with hi
    set j := α (Sum.inr m) with hj
    have key : ∀ i', α = Finsupp.single (Sum.inl m) i' + Finsupp.single (Sum.inr m) (N - i') →
        i = i' ∧ j = N - i' := by
      intro i' h
      constructor
      · rw [hi, h]; simp
      · rw [hj, h]; simp
    by_cases hs : α = Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j
    · rw [if_pos hs]
      by_cases hin : 0 < i ∧ i < N ∧ j = N - i
      · obtain ⟨w, hw1, hw2⟩ := ht m i hin.1 hin.2.1
        refine ⟨w, ?_, ?_⟩
        · rw [Finset.sum_eq_single_of_mem i (Finset.mem_Ioo.2 ⟨hin.1, hin.2.1⟩)]
          · rw [if_pos (hs.trans (by rw [hin.2.2])), hw1]
          · intro i' _ hne; rw [if_neg]; intro h; exact hne (key i' h).1.symm
        · rw [hw2]; simp only [ha]; rw [← hin.2.2, ← hs]
      · refine ⟨0, ?_, ?_⟩
        · rw [Finset.sum_eq_zero, mul_zero, map_zero]
          intro i' hi'; rw [if_neg]; intro h
          obtain ⟨e1, e2⟩ := key i' h
          rw [Finset.mem_Ioo] at hi'
          exact hin ⟨e1 ▸ hi'.1, e1 ▸ hi'.2, e1 ▸ e2⟩
        · rw [map_zero]
          by_cases hd : i + j = N
          · have : i = 0 ∨ i = N := by omega
            rcases this with h0 | h0
            · have : α = Finsupp.single (Sum.inr m) N := by
                rw [hs, h0, Finsupp.single_zero, zero_add]; congr 1; omega
              rw [this, hzero']
            · have : α = Finsupp.single (Sum.inl m) N := by
                rw [hs, h0, (by omega : j = 0), Finsupp.single_zero, add_zero]
              rw [this, hzero]
          · refine (hhom α ?_).symm
            rw [hs, map_add, Finsupp.degree_single, Finsupp.degree_single]; exact hd
    · rw [if_neg hs]
      refine ⟨0, ?_, by simp⟩
      rw [Finset.sum_eq_zero, mul_zero, map_zero]
      intro i' _; rw [if_neg]; intro h
      apply hs; obtain ⟨e1, e2⟩ := key i' h; rw [e1, e2]; exact h
  refine ⟨Katz.lift p bN + ∑ m, t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k)), ?_, ?_⟩
  · intro α hα
    rw [map_add, map_sum, coeff_lift, hbNc, if_neg hα, WittVector.teichmuller_zero, map_zero,
      zero_add]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [map_smul, coeff_X_pow, if_neg, smul_zero]
    intro h; apply hα; rw [h, Finsupp.degree_single]
  · have h1 : Red p (cob1 (addLaw (Fr p k) d) (Katz.lift p bN)) (cob1 (addLaw k d) bN) := by
      rw [← lift_addLaw p k d]
      exact ((GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (hconst k)).2.1 _ _
        ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.1 bN)).1
    have h2 : Red p (∑ m, cob1 (addLaw (Fr p k) d) (t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k))))
        (∑ m, cm m) := by
      refine redSum _ _ _ fun m _ => ?_
      rw [formalCoboundary_smul hconstFr]; exact redm m
    have := ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ h1 h2).1
    rw [formalCoboundary_add hconstFr, cobSum]
    rwa [← hdec] at this

end GlobalTheory.LazardHomog
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_cocycle_additiveLaw_reduction_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) k), 2 ≤ N → IsCoc (addLaw k d) c → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ Red p (cob1 (addLaw (Fr p k) d) h) c := by
  atlas_forward_decl GlobalTheory.LazardHomog.homogCoc_red_cob
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem algebraMap_pow_ne_zero (m : ℕ) :
    algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) ≠ 0 := fun h =>
  pow_ne_zero m (WittVector.p_nonzero p k)
    (IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [h, map_zero]))

theorem coeff_wsmul {σ : Type} (w : WittVector p k) (f : MvPowerSeries σ (Fr p k))
    (α : σ →₀ ℕ) : coeff α (w • f) = algebraMap (WittVector p k) (Fr p k) w * coeff α f := by
  rw [← Algebra.smul_def]; rfl

theorem mem_one_of_p_smul {σ : Type} (f : MvPowerSeries σ (Fr p k))
    (hf : (p : WittVector p k) • f ∈ intBy p k σ (p : WittVector p k)) : f ∈ intBy p k σ 1 := by
  intro α
  obtain ⟨w, hw⟩ := hf α
  refine ⟨w, ?_⟩
  rw [coeff_wsmul, map_mul] at hw
  rw [one_mul]
  have h0 := algebraMap_pow_ne_zero p k 1
  rw [pow_one] at h0
  exact mul_left_cancel₀ h0 hw

theorem exists_pow_smul_mem {d N : ℕ} (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
    (he : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) :
    ∃ m : ℕ, ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) := by
  classical
  have hfin := Finsupp.finite_of_degree_le (σ := Fin d ⊕ Fin d) N
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (WittVector p k)) (hfin.toFinset.image fun γ => coeff γ e)
  have hb0 : (b : WittVector p k) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (b : WittVector p k) hb0
  refine ⟨n + 1, fun γ => ?_⟩
  by_cases hγ : γ.degree = N
  · have hmem : coeff γ e ∈ hfin.toFinset.image fun γ => coeff γ e :=
      Finset.mem_image.2 ⟨γ, by simp [hγ], rfl⟩
    obtain ⟨w, hw⟩ := hb _ hmem
    refine ⟨((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) * w, ?_⟩
    have hw' : algebraMap (WittVector p k) (Fr p k) w =
        algebraMap (WittVector p k) (Fr p k) (b : WittVector p k) * coeff γ e := by
      rw [hw, Algebra.smul_def]
    have hu1 : algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) *
        algebraMap (WittVector p k) (Fr p k) (u : WittVector p k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_mul, map_pow] at hw'
    rw [coeff_wsmul, map_mul, map_mul, map_pow, pow_succ]
    linear_combination (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) *
      algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k)) * hw' +
      (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) ^ n *
        algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) * coeff γ e) * hu1
  · refine ⟨0, ?_⟩
    rw [coeff_wsmul, he γ hγ]
    simp

theorem lift_addLaw (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext γ
  rw [coeff_lift]
  simp only [addLaw, map_add, coeff_X]
  by_cases h1 : γ = Finsupp.single (Sum.inl i) 1
  · have h2 : γ ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h; exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    simp only [if_pos h1, if_neg h2, add_zero, map_one, map_one]
  · by_cases h2 : γ = Finsupp.single (Sum.inr i) 1
    · simp only [if_neg h1, if_pos h2, zero_add, map_one, map_one]
    · simp only [if_neg h1, if_neg h2, add_zero, WittVector.teichmuller_zero, map_zero]

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem step (d N : ℕ) (hN : 2 ≤ N) (m : ℕ) : ∀ e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ (p : WittVector p k) →
    swap e - e ∈ intBy p k _ (p : WittVector p k) →
    ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ (p : WittVector p k) := by
  have hconst : ∀ i, constantCoeff (addLaw (Fr p k) d i) = 0 := fun i => by simp [addLaw]
  have hA := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst 0
  have hlaw : IsLaw (addLaw (Fr p k) d) := hA.2.2.2.2.1
  have hcob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconst 0 0
    rwa [zero_smul, zero_smul] at this
  have hR := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hR3 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ (Fin d ⊕ Fin d))
  have hRC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (fun i => by simp [addLaw])
  rw [lift_addLaw] at hRC
  induction m with
  | zero =>
    intro e _ _ _ hm
    refine ⟨0, fun _ _ => by simp, ?_⟩
    rw [hcob0, sub_zero]
    simpa using hm
  | succ m ih =>
    intro e he hcb hsw hm
    have hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)), ((p : WittVector p k) ^ m) • x =
        algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) • x :=
      fun x => (algebraMap_smul (Fr p k) _ x).symm
    have hQ := algebraMap_pow_ne_zero p k m
    rw [pow_succ', mul_smul] at hm
    have he' := mem_one_of_p_smul p k _ hm
    obtain ⟨c, hc⟩ := (hR.1 _).1 he'
    have hcb' : cob2 (addLaw (Fr p k) d) (((p : WittVector p k) ^ m) • e) ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).1, ← hsm]
      exact Submodule.smul_mem _ _ hcb
    have hsw' : swap (((p : WittVector p k) ^ m) • e) - ((p : WittVector p k) ^ m) • e ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).2, ← smul_sub, ← hsm]
      exact Submodule.smul_mem _ _ hsw
    obtain ⟨hr2, hrs⟩ := hRC.1 _ _ hc
    have hc2 : cob2 (addLaw k d) c = 0 := hR3.2.1 _ _ _ hr2 ((hR3.2.2.2.2.2.1 _).1 hcb')
    have hcs : swap c = c := sub_eq_zero.1
      (hR.2.1 _ _ _ (hR.2.2.2.1 _ _ _ _ hrs hc).2 ((hR.2.2.2.2.2.1 _).1 hsw'))
    have hch : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0 := by
      intro γ hγ
      obtain ⟨w, hw1, hw2⟩ := hc γ
      rw [coeff_wsmul, he γ hγ, mul_zero] at hw1
      have hw0 : w = 0 := IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [← hw1, map_zero])
      rw [← hw2, hw0, map_zero]
    obtain ⟨h', hh', hred⟩ := GlobalTheory.T.homogeneous_cocycle_additiveLaw_reduction_coboundary p k d N c hN ⟨hc2, hcs⟩ hch
    have hdiff : ((p : WittVector p k) ^ m) • e - cob1 (addLaw (Fr p k) d) h' ∈
        intBy p k _ (p : WittVector p k) := by
      have := (hR.2.2.2.1 _ _ _ _ hc hred).2
      rw [sub_self] at this
      exact (hR.2.2.2.2.2.1 _).2 this
    have hcobh1 : ((p : WittVector p k) ^ m) • cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') =
        cob1 (addLaw (Fr p k) d) h' := by
      rw [hsm, ← formalCoboundary_smul hconst, smul_smul, mul_inv_cancel₀ hQ, one_smul]
    have hh1 : ∀ α : Fin d →₀ ℕ, α.degree ≠ N →
        coeff α ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') = 0 := by
      intro α hα
      rw [coeff_smul, hh' α hα, mul_zero]
    have hcoc := (GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst
      ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h')).2.2.2.2.2 hlaw
    obtain ⟨h2, hh2, hfin⟩ := ih (e - cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h'))
      (fun γ hγ => by
        rw [map_sub, he γ hγ, (GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N).1 _ hh1 γ hγ, sub_zero])
      (by rw [((hA.2.2.1) e _).2.1, hcoc.1, sub_zero]; exact hcb)
      (by
        rw [((hA.2.2.1) e _).2.2, hcoc.2]
        convert hsw using 1
        abel)
      (by rw [smul_sub, hcobh1]; exact hdiff)
    refine ⟨(algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h' + h2,
      fun α hα => by rw [map_add, hh1 α hα, hh2 α hα, add_zero], ?_⟩
    rw [formalCoboundary_add hconst]
    convert hfin using 1
    abel

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz

theorem lazard_mod_p_frac : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d N : ℕ) (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)), 2 ≤ N →
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ p → swap e - e ∈ intBy p k _ p →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ p := by
  intro p _ k _ _ _ d N e hN he hcb hsw
  obtain ⟨m, hm⟩ := LazardModP.exists_pow_smul_mem p k e he
  exact LazardModP.step p k d N hN m e he hcb hsw hm

end GlobalTheory.Katz
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lazard_additive_law_wittVectorFractionField_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)), 2 ≤ N → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) → cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ p → swap e - e ∈ intBy p k _ p → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ p := by
  atlas_forward_decl GlobalTheory.Katz.lazard_mod_p_frac
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt {R τ : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (M : ℕ)
    (hc : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < M → coeff α c = 0) :
    ∀ γ : τ →₀ ℕ, γ.degree < M → coeff γ (at2 c u v) = 0 := by
  intro γ hγ
  have ha : ∀ s, constantCoeff (Sum.elim u v s) = 0 := by
    rintro (i | i)
    · exact hu i
    · exact hv i
  have hs : HasSubst (Sum.elim u v) := hasSubst_of_constantCoeff_zero ha
  have h1 : (1 : ℕ∞) ≤ ⨅ s, (Sum.elim u v s).order := le_iInf fun s => by
    apply MvPowerSeries.le_order
    intro δ hδ
    have h0 : δ.degree = 0 := by exact_mod_cast ENat.lt_one_iff_eq_zero.mp hδ
    rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact ha s
  have h2 : (M : ℕ∞) ≤ c.order := MvPowerSeries.le_order fun δ hδ => hc δ (by exact_mod_cast hδ)
  have h3 := le_order_subst hs c
  unfold at2
  apply coeff_of_lt_order
  calc (γ.degree : ℕ∞) < M := by exact_mod_cast hγ
    _ ≤ 1 * c.order := by rw [one_mul]; exact h2
    _ ≤ (⨅ s, (Sum.elim u v s).order) * c.order := mul_le_mul_left h1 _
    _ ≤ _ := h3

theorem coeff_formalGroupLawCoboundaryTwo_eq_zero_of_degree_lt {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (M : ℕ)
    (hc : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < M → coeff α c = 0) :
    ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree < M → coeff γ (cob2 μ c) = 0 := by
  intro γ hγ
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    rw [← coeff_zero_eq_constantCoeff_apply]
    refine coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt (μ i) u v hu hv 1 (fun α hα => ?_) 0 (by simp)
    have h0 : α.degree = 0 := by omega
    rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact hμ i
  unfold cob2
  simp only [map_add, map_sub]
  rw [coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx2 hx3 M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ (hop _ _ hx1 hx2) hx3 M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx1 (hop _ _ hx2 hx3) M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx1 hx2 M hc γ hγ]
  simp

theorem degree_mapDomain_swap_ord {d : ℕ} (γ : Fin d ⊕ Fin d →₀ ℕ) :
    (γ.mapDomain Sum.swap).degree = γ.degree := by
  induction γ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]
  | single a n => rw [Finsupp.mapDomain_single, Finsupp.degree_single, Finsupp.degree_single]

end GlobalTheory.Katz

theorem GlobalTheory.Katz.quasiLog_approx_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc N f hN hf hlow
  have hL0 : ∀ i, constantCoeff ((fun i => Katz.lift p (μ i)) i) = 0 :=
    fun i => constantCoeff_lift p (hμ.const i)
  have CC := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL0 0
  have Q := GlobalTheory.T.coboundaryOne_teichmullerLift_isCocycle_mod_p p k d μ hμ f hf
  have RD := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have RD3 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ (Fin d ⊕ Fin d))
  have RC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have LIN := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have LEAD := GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun i => Katz.lift p (μ i)) N (fun i α hα => (LIN i α hα).2)
  have HOM := GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N
  obtain ⟨g, hg⟩ : ∃ g, g = cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c := ⟨_, rfl⟩
  rw [← hg] at hlow

  have hg2 : cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ (p : WittVector p k) := by
    have h1 : Red p (cob2 (fun i => Katz.lift p (μ i)) (Katz.lift p c)) 0 := by
      have := (RC.1 (Katz.lift p c) c (RD.2.2.1 c)).1
      rwa [hc.1] at this
    rw [hg, (CC.2.2.1 _ _).2.1]
    exact sub_mem Q.1 ((RD3.2.2.2.2.2.1 _).2 h1)
  have hgs : swap g - g ∈ intBy p k _ (p : WittVector p k) := by
    have h1 : Red p (swap (Katz.lift p c) - Katz.lift p c) 0 := by
      have a := (RC.1 (Katz.lift p c) c (RD.2.2.1 c)).2
      rw [hc.2] at a
      have := (RD.2.2.2.1 _ _ _ _ a (RD.2.2.1 c)).2
      rwa [sub_self] at this
    have : swap g - g = (swap (cob1 (fun i => Katz.lift p (μ i)) f) -
        cob1 (fun i => Katz.lift p (μ i)) f) - (swap (Katz.lift p c) - Katz.lift p c) := by
      rw [hg, (CC.2.2.1 _ _).2.2]; abel
    rw [this]
    exact sub_mem Q.2 ((RD.2.2.2.2.2.1 _).2 h1)

  obtain ⟨e, he⟩ : ∃ e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
      ∀ γ, coeff γ e = if γ.degree = N then coeff γ g else 0 :=
    ⟨fun γ => if γ.degree = N then coeff γ g else 0, fun γ => rfl⟩
  obtain ⟨low, hlo⟩ : ∃ low : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
      ∀ γ, coeff γ low = if γ.degree < N then coeff γ g else 0 :=
    ⟨fun γ => if γ.degree < N then coeff γ g else 0, fun γ => rfl⟩
  have hhigh : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → coeff γ (g - low - e) = 0 := by
    intro γ hγ
    rw [map_sub, map_sub, he, hlo]
    by_cases h1 : γ.degree < N
    · rw [if_pos h1, if_neg (by omega)]; ring
    · rw [if_neg h1, if_pos (by omega)]; ring
  have hlowI : low ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    rw [hlo]
    by_cases h1 : γ.degree < N
    · rw [if_pos h1]; exact hlow γ h1
    · rw [if_neg h1]; exact ⟨0, by simp⟩
  have ehom : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0 := by
    intro γ hγ; rw [he, if_neg hγ]
  have eord : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → coeff γ e = 0 :=
    fun γ hγ => ehom γ (by omega)
  have hcob2e : cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    by_cases hγ : γ.degree = N
    · rw [← LEAD.2 e eord γ hγ.le]
      have hsplit : e = g - low - (g - low - e) := by abel
      have hz := coeff_formalGroupLawCoboundaryTwo_eq_zero_of_degree_lt (fun i => Katz.lift p (μ i)) hL0
        (g - low - e) (N + 1) hhigh γ (by omega)
      obtain ⟨w1, hw1⟩ := hg2 γ
      obtain ⟨w2, hw2⟩ := (RC.2.2.2 _ low hlowI).1 γ
      refine ⟨w1 - w2, ?_⟩
      rw [hsplit, (CC.2.2.1 _ _).2.1, (CC.2.2.1 _ _).2.1, map_sub, map_sub, hz, hw1, hw2,
        mul_sub, map_sub, sub_zero]
    · rw [HOM.2.1 e ehom γ hγ]; exact ⟨0, by simp⟩
  have hswape : swap e - e ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    rw [map_sub, HOM.2.2.1, he, he, degree_mapDomain_swap_ord]
    by_cases hγ : γ.degree = N
    · rw [if_pos hγ, if_pos hγ]
      obtain ⟨w, hw⟩ := hgs γ
      rw [map_sub, HOM.2.2.1] at hw
      exact ⟨w, hw⟩
    · rw [if_neg hγ, if_neg hγ]; exact ⟨0, by simp⟩
  obtain ⟨h, hhom, hint⟩ := GlobalTheory.T.lazard_additive_law_wittVectorFractionField_mod_p p k d N e hN ehom hcob2e hswape
  have hord : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0 := fun α hα => hhom α (by omega)
  have hsub : cob1 (fun i => Katz.lift p (μ i)) (f - h) =
      cob1 (fun i => Katz.lift p (μ i)) f - cob1 (fun i => Katz.lift p (μ i)) h := by
    rw [eq_sub_iff_add_eq, ← formalCoboundary_add hL0, sub_add_cancel]
  have K : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k,
      coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) =
        algebraMap (WittVector p k) (Fr p k) (p * w) := by
    intro γ hγ
    have e1 : cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c =
        g - cob1 (fun i => Katz.lift p (μ i)) h := by rw [hsub, hg]; abel
    rw [e1, map_sub]
    obtain ⟨hL1, hL2⟩ := LEAD.1 h hord γ
    by_cases h1 : γ.degree < N
    · rw [hL1 h1, sub_zero]; exact hlow γ h1
    · have hN' : γ.degree = N := by omega
      rw [hL2 hN'.le]
      have : coeff γ g = coeff γ e := by rw [he, if_pos hN']
      rw [this, ← map_sub]
      exact hint γ
  have hnegq : -h ∈ quasiInt p k (Fin d) := by
    intro α i
    by_cases hα : α.degree = N
    · refine GlobalTheory.T.degree_part_integralDifferential_of_coboundary p k d μ hμ N f (-h) hN hf
        (fun β hβ => by rw [map_neg, hord β hβ, neg_zero]) (fun γ hγ => ?_) α i hα
      obtain ⟨w, hw⟩ := K γ (by omega)
      refine ⟨p * w + WittVector.teichmuller p (coeff γ c), ?_⟩
      rw [← sub_eq_add_neg, map_add, ← hw, map_sub, coeff_lift]; ring
    · rw [map_neg, hhom α hα, neg_zero, mul_zero]; exact ⟨0, by simp⟩
  refine ⟨h, hhom, sub_mem hf ((neg_mem_iff).1 hnegq), K⟩
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_successive_approximation_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  atlas_forward_decl GlobalTheory.Katz.quasiLog_approx_step
end
