module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tt_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'')
    (h4 : i' = i'') (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = Ht.cast (h1.trans h3) (h2.trans h4) a := by
  subst h1; subst h2; subst h3; subst h4; rfl

theorem tt_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f _ _ (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f _ _ a) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_right {q : ℕ} {E : Spc} {n i m j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (b : Ht q E m j) : cup q a (Ht.cast h1 h2 b) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_left {q : ℕ} {E : Spc} {n i m j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i)
    (b : Ht q E m j) : cup q (Ht.cast h1 h2 a) b = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tauTop : LeafTauTop := by
  intro H q _ d R _ n i x a
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hr : DivisorRingCompatibility := H.2.2.2.2.2.1
  let e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)) :=
    Fin.lastCases (motive := fun j : Fin (d + 1) =>
        Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)))
      (x.cast (by simp) (by simp))
      (fun j => (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring) (by simp only [Fin.val_castSucc]; ring))
  refine ⟨e, by simp [e], ?_⟩
  have he : ∀ j : Fin d, e j.castSucc = (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring)
      (by simp only [Fin.val_castSucc]; ring) := fun j => by simp [e]
  have hl : e (Fin.last d) = x.cast (by simp) (by simp) := by simp [e]
  unfold poly

  rw [map_add (f := _), map_sum, Fin.sum_univ_castSucc]
  refine (add_comm _ _).trans ?_
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [he, tt_pull_cast, tt_cup_cast_left, (h6 q).1, (hr q _).2.1, tt_cup_cast_right]
    repeat rw [tt_cast_cast]
    rfl
  · rw [hl, tt_pull_cast, tt_cup_cast_left]
    repeat rw [tt_cast_cast]
    rfl

theorem LeafTauTop_of : LeafTauTop := tauTop

end LateralTheory.CohomologicalPurity.Thom
