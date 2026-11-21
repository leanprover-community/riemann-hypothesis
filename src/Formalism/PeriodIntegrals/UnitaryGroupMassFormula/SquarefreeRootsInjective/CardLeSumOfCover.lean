import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.DivCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.TwoPowCardPrimeFactorsLe

open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

open PI.SqfLab

def LS (g r n : ℕ) : Finset ℕ := n.primeFactors.filter (fun ℓ => ℓ ∉ BB r g)

def WA (g e j ℓ : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  (nthRoots ((g ^ j - 1) * Lp g e ℓ) (1 : Fbar g)).toFinset.filter
    (fun w => (minpoly (ZMod g) w).natDegree = e)

def YB (g e' : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  ((X ^ (g ^ e') - X : (Fbar g)[X]).roots.toFinset).filter
    (fun y => (minpoly (ZMod g) y).natDegree = e')

def XB (g e ℓ : ℕ) [Fact g.Prime] (y : Fbar g) : Finset (Fbar g) :=
  (nthRoots (Lp g e ℓ) ((primeToPart ℓ y) ^ Lp g e ℓ)).toFinset.filter
    (fun x => (minpoly (ZMod g) x).natDegree = e)

def SA (g r : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2), ∑ ℓ ∈ LS g r (g ^ e - 1),
    (g ^ j - 1) * Lp g e ℓ * g ^ (r - e)

def SB (g r : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)), ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
    g ^ e' * Lp g e ℓ * g ^ (r - e - e')


theorem minpoly_monic' {g : ℕ} [Fact g.Prime] (w : Fbar g) : (minpoly (ZMod g) w).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral w)

def PA (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 2 r, ∃ j ∈ Finset.Icc 1 (e / 2),
    ∃ ℓ ∈ LS g r (g ^ e - 1), ∃ w ∈ WA g e j ℓ, minpoly (ZMod g) w ∣ f

def PB (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 1 r, ∃ e' ∈ Finset.Icc 1 (min e (r - e)),
    ∃ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∃ y ∈ YB g e', ∃ x ∈ XB g e ℓ y,
      minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f




theorem cardA (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PA g r)).card ≤ SA g r := by
  calc (T.filter (PA g r)).card ≤ ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2),
      ∑ ℓ ∈ LS g r (g ^ e - 1), ∑ w ∈ WA g e j ℓ,
        (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 2 r).biUnion fun e =>
          (Finset.Icc 1 (e / 2)).biUnion fun j => (LS g r (g ^ e - 1)).biUnion fun ℓ =>
            (WA g e j ℓ).biUnion fun w => T.filter (fun f => minpoly (ZMod g) w ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, j, hj, ℓ, hℓ, w, hw, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, j, hj, ℓ, hℓ, w, hw, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SA g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun ℓ _ => ?_
        calc ∑ w ∈ WA g e j ℓ, (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card
            ≤ ∑ w ∈ WA g e j ℓ, g ^ (r - e) := by
              refine Finset.sum_le_sum fun w hw => ?_
              have h1 := divCount r T hmon _ (minpoly_monic' w)
              have h2 : (minpoly (ZMod g) w).natDegree = e := (Finset.mem_filter.1 hw).2
              rw [h2] at h1
              exact h1
          _ = (WA g e j ℓ).card * g ^ (r - e) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (g ^ j - 1) * Lp g e ℓ * g ^ (r - e) :=
              Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))

theorem cardB (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PB g r)).card ≤ SB g r := by
  have hg2 : 1 < g := hg.out.one_lt
  calc (T.filter (PB g r)).card ≤ ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)),
      ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
        (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 1 r).biUnion fun e =>
          (Finset.Icc 1 (min e (r - e))).biUnion fun e' => (LS g r ((g ^ e - 1) * (g ^ e' - 1))).biUnion fun ℓ =>
            (YB g e').biUnion fun y => (XB g e ℓ y).biUnion fun x =>
              T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, e', he', ℓ, hℓ, y, hy, x, hx, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, e', he', ℓ, hℓ, y, hy, x, hx, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e' _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SB g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun e' he' =>
          Finset.sum_le_sum fun ℓ _ => ?_
        have he1 : 1 ≤ e' := (Finset.mem_Icc.1 he').1
        calc ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
              (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card
            ≤ ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y, g ^ (r - e - e') := by
              refine Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun x hx => ?_
              have h1 := divCount r T hmon _ ((minpoly_monic' x).mul (minpoly_monic' y))
              have h2 : (minpoly (ZMod g) x * minpoly (ZMod g) y).natDegree = e + e' := by
                rw [(minpoly_monic' x).natDegree_mul (minpoly_monic' y),
                  (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
              rw [h2] at h1
              rw [Nat.sub_sub]
              exact h1
          _ = ∑ y ∈ YB g e', (XB g e ℓ y).card * g ^ (r - e - e') := by
              simp only [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ y ∈ YB g e', Lp g e ℓ * g ^ (r - e - e') :=
              Finset.sum_le_sum fun y _ => Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))
          _ = (YB g e').card * (Lp g e ℓ * g ^ (r - e - e')) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ g ^ e' * (Lp g e ℓ * g ^ (r - e - e')) :=
              Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans
                (card_roots_X_pow_sub_X_le _ (Nat.one_lt_pow (by omega) hg2)))
          _ = g ^ e' * Lp g e ℓ * g ^ (r - e - e') := by rw [mul_assoc]


end PI.SqfRootsInj.W
