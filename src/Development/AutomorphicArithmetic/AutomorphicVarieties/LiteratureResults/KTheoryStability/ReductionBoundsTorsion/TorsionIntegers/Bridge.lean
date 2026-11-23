module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.FinalOdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.V.KL

namespace PositivityTheory.KB

theorem lev_zk (l n : ℕ) : ∀ t, UpperTheory.V.ZK.lev l n t = lev l n t
  | 0 => rfl
  | t + 1 => congrArg (l * ·) (lev_zk l n t)

private theorem step_heq (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) (m c : ℕ) {a b : ℕ} (e : a = b)
    (u : grpH (GL (Fin a) R) m) (v : grpH (GL (Fin b) R) m) (h : HEq u v) :
    HEq ((grpHMap (UpperTheory.V.ZK.psi R l a) m).hom u -
        c • (grpHMap (stab R a (l * a) (Nat.le_mul_of_pos_left _ hl)) m).hom u)
      ((grpHMap (psi R l b) m).hom v - c • (grpHMap (stab R b (l * b) (Nat.le_mul_of_pos_left _ hl)) m).hom v) := by
  subst e
  obtain rfl := eq_of_heq h
  rfl

theorem zSeq_zk (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n m : ℕ} (x : grpH (GL (Fin n) R) m) :
    ∀ t, HEq (UpperTheory.V.ZK.zSeq R hl x t) (zSeq R hl x t)
  | 0 => HEq.rfl
  | t + 1 => step_heq R hl m (l ^ (t + 2)) (lev_zk l n t) _ _ (zSeq_zk R hl x t)

private theorem rank_heq (R : Type) [CommRing R] (m : ℕ) {X : Type} {a b : ℕ} (e : a = b)
    (f : X → grpH (GL (Fin a) R) m) (g : X → grpH (GL (Fin b) R) m) (h : ∀ x, HEq (f x) (g x)) :
    Module.rank ℤ (Submodule.span ℤ (Set.range f)) = Module.rank ℤ (Submodule.span ℤ (Set.range g)) := by
  subst e
  obtain rfl : f = g := funext fun x => eq_of_heq (h x)
  rfl

theorem bOdd_zk : UpperTheory.V.ZK.BOdd := fun L _ _ hL k hk hr l hl n hn =>
  (rank_heq _ _ (lev_zk l n k) _ _ fun x => zSeq_zk _ hl x k).le.trans (bStarOdd L hL k hk hr l hl n hn)

end PositivityTheory.KB
