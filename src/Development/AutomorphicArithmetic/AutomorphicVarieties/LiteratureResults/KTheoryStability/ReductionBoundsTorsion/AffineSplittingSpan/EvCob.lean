module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.InclInj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral

namespace EvaluationCoboundary

open PositivityTheory.KB

theorem ev_eq {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) z := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem key {G : Type} [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ) (he : Inv (MonoidHom.id G) e)
    (g : Fin (j + 1) → G) :
    dC e (fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) =
      ev (MonoidHom.id G) e 1 (bd G j (Finsupp.single g 1)) := by

  rw [ev_eq, bd, Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum,
  Finsupp.linearCombination_single, dC, Fin.sum_univ_succ]
  simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.succAbove_zero, one_smul,
    Fin.val_zero, pow_zero, one_mul, map_smul, Finsupp.linearCombination_single, Fin.val_succ]
  congr 1
  · have h := he (g 0) fun i => Fin.partialProd (fun i => g i.succ) i
    simp only [MonoidHom.id_apply, smul_eq_mul] at h
    rw [← h]
    congr 1
    funext i
    rw [Fin.partialProd_succ']
    rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fin.partialProd_contractNth]
    rfl

end EvaluationCoboundary

theorem evCob : EvCob := by
  intro G _ j e he z hz
  have h : ∀ w : Chn G (j + 1), ev (MonoidHom.id G) (dC e) 1 w =
      ev (MonoidHom.id G) e 1 (bd G j w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp [ev]
    | add a b ha hb =>
      rw [map_add (f := _), EvaluationCoboundary.ev_eq, map_add (f := _), ← EvaluationCoboundary.ev_eq, ← EvaluationCoboundary.ev_eq, ha, hb,
        EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq e (bd G j b), ← map_add, ← EvaluationCoboundary.ev_eq]
    | single g r =>
      rw [EvaluationCoboundary.ev_eq, Finsupp.linearCombination_single, EvaluationCoboundary.key j e he g,
        ← Finsupp.smul_single_one, map_smul, EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq, map_smul]
      rw [one_smul, ← map_smul, ← map_smul, Finsupp.smul_single_one]
  rw [h, hz]
  simp [ev]

end PositivityTheory.KB.SplitAffineSpectral

end
