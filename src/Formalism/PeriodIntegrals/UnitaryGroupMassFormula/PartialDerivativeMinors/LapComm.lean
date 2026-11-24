module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem pderiv_pderiv_comm {σ R : Type} [CommRing R] (v w : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv w f) = MvPolynomial.pderiv w (MvPolynomial.pderiv v f) := by
  have hX : ∀ i j k : σ, MvPolynomial.pderiv i (MvPolynomial.pderiv j (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
    intro i j k
    by_cases h : k = j
    · subst h; simp
    · simp [MvPolynomial.pderiv_X_of_ne h]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), hX, mul_zero, zero_add, hp]
    ring

theorem pd_comm {H : Type} {N0 N1 : ℕ} (v w : XZ (Bool × H) N0 N1) :
    Commute (pd (H := H) (N0 := N0) (N1 := N1) v) (pd w) := by
  refine LinearMap.ext fun f => ?_
  exact pderiv_pderiv_comm (R := ℤ) v w f

theorem pLapComm : PLapComm := by
  intro H N0 N1 t t'
  unfold lapT
  refine Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_
  refine Commute.sum_right _ _ _ fun a' _ => Commute.sum_right _ _ _ fun b' _ => ?_
  exact ((pd_comm _ _).mul_right (pd_comm _ _)).mul_left ((pd_comm _ _).mul_right (pd_comm _ _))

end PI.EntAtD.W
