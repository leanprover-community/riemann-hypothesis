module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

theorem nPt_append_one (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j + 1 ≤ P.r) (c : ℂ) :
    TBB.nPt P.k P.r TT (a ++ [(1, c)]) = TBB.nPt P.k P.r TT a * KB.levW P (j + 1) c := by
  let GG := D.ptGG TT (a ++ [(1, c)])
  let GG' := D.ptGG TT a
  have happend : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l = j + 1 →
      C.nAux P.k P.r GG (fun _ _ => 1) b (l ++ [(1, c)]) =
        C.nAux P.k P.r GG' (fun _ _ => 1) b l * KB.levW P (j + 1) c := by
    intro l
    induction l with
    | nil =>
      intro b hb
      change b + 0 = j + 1 at hb
      rw [Nat.add_zero] at hb
      subst b
      have htop : j + 1 ≠ P.r + 1 := by omega
      have hexp : C.Mlev P.k P.r (j + 1) + 1 - 3 = C.Mlev P.k P.r (j + 1) - 2 := by ring
      simp only [List.nil_append, C.nAux, KB.levW, Nat.add_sub_cancel, htop, false_and,
        if_false, Nat.cast_one, one_mul, mul_one, hexp]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) = j + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [List.cons_append, C.nAux, htop, false_and, if_false, ih (b + s) (by omega), mul_assoc]
  exact happend a 1 (by rw [ha.2, Nat.add_comm])

theorem nPt_nonneg_loc (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j ≤ P.r) :
    0 ≤ TBB.nPt P.k P.r TT a := by
  have hnonneg : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l ≤ P.r + 1 →
      0 ≤ C.nAux P.k P.r (D.ptGG TT a) (fun _ _ => 1) b l := by
    intro l
    induction l with
    | nil =>
      intro b _
      simp [C.nAux]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) ≤ P.r + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [C.nAux, htop, false_and, if_false, one_mul]
      exact mul_nonneg (zpow_nonneg (norm_nonneg _) _) (ih (b + s) (by omega))
  exact hnonneg a 1 (by rw [ha.2]; omega)

theorem levW_nonneg_low (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (c : ℂ) : 0 ≤ KB.levW P (j + 1) c := by
  simp only [KB.levW]
  rw [if_neg (by omega)]
  exact zpow_nonneg (norm_nonneg _) _

end

end Formalism.FourierDecayAlt.P.CutBP
