import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G
open scoped BigOperators

variable {D : D7} {L : SizeData₂ D}

def posOn (D : D7) (h t0 : HH D) (T : Finset (HH D)) : Finset (Fin (addOrderOf h)) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • h ∈ T)

def BadOrb (X : Inst D L) (h t : HH D) (T : Finset (HH D)) : Prop :=
  ¬ IsGoodOrbit (addOrderOf h) (posOn D h (X.bs h t) T) (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1
    (hG L.sc) L.sc.x

open Classical in

def BadProb (X : Inst D L) (Cb : ℝ) : Prop :=
  ∀ h : HH D, L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf h : ℝ) → ∀ t : HH D,
    (∑ T : Finset (HH D), if t ∈ T ∧ BadOrb X h t T then UnusedSlot33.bern L.sc.delta1 T else 0) ≤
      (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1

open Classical in

def TopsOK (X : Inst D L) (Cb : ℝ) (T : Finset (HH D)) : Prop :=
  L.sc.delta1 * D.R.n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * L.sc.delta1 * D.R.n ∧
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((T.filter (fun t => BadOrb X (hP D p) t T)).card : ℝ) ≤
    4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p

theorem delta1_pos (s : Scale) : 0 < s.delta1 := by
  unfold Scale.delta1
  exact Real.rpow_pos_of_pos (by linarith [s.one_lt_alt]) _

theorem delta1_le_one (s : Scale) : s.delta1 ≤ 1 := by
  unfold Scale.delta1
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt s.one_lt_alt) (by linarith [s.eps_pos])



theorem frobenius_step_large_order {p : ℕ} (hp : IsResidueClassZero D p) : stepP D p = hP D p := by
  simp [stepP, IsSg, hp]


theorem primes_eq (L : SizeData₂ D) :
    (AuxBlock8.primesResidueBelow D L.sc.X').filter
      (fun p => L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ)) = largeOrderResiduePrimes L := by
  ext p
  unfold largeOrderResiduePrimes AuxBlock8.primesResidueBelow
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨h1, h2, h4, h5⟩
  · rintro ⟨h1, h2, h4, h5⟩
    exact ⟨⟨h1, h2, Nat.lt_ceil.mp h1, h4⟩, h5⟩


end Formalism.MainNotions.J

end
