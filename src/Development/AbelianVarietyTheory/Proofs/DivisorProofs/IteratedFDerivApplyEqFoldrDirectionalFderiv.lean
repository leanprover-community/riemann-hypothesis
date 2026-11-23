module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem iteratedFDeriv_apply_eq_foldr_fderiv :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  intro E _ _ g hg j
  induction j with
  | zero =>
    intro m x
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m x
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]
    have hfun : (List.ofFn (fun i : Fin n => m i.succ)).foldr (fun v g' => fun z => fderiv ℝ g' z v) g
        = fun z => iteratedFDeriv ℝ n g z (Fin.tail m) := by
      funext z
      exact (ih (Fin.tail m) z).symm
    simp only [hfun]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.differentiable_iteratedFDeriv (by first | exact_mod_cast ENat.coe_lt_top n | simp | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top n))) x
    rw [fderiv_continuousMultilinear_apply_const_apply hd]

end GlobalTheory
