import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.MonicFintype

open Polynomial Finset

noncomputable section

namespace PI.SqfDivDeg.W

open Classical

def rts {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Finset (ZMod g) :=
  univ.filter (fun c => f.IsRoot c)

theorem rt_one (g : ℕ) [Fact g.Prime] : Rt g 1 = Mon g 1 := by
  unfold Rt
  apply Finset.filter_true_of_mem
  intro p hp
  rw [mem_Mon] at hp
  exact exists_root_of_degree_eq_one
    (by rw [degree_eq_natDegree hp.1.ne_zero, hp.2, Nat.cast_one])




theorem pt (k : ℕ) : 2 * k ≤ (k * k - k) + 2 * (if k = 0 then 0 else 1) := by
  match k with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
    have h : (k + 2) * (k + 2) - (k + 2) = (k + 2) * (k + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h]
    simp
    nlinarith





end PI.SqfDivDeg.W
