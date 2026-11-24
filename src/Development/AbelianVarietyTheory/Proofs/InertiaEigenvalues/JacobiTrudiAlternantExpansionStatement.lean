module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansion
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.jacobi_trudi_alternant_expansion : ∀ {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A),
    GlobalTheory.JSW.alternant A m (GlobalTheory.JSW.staircase m) *
                 ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ GlobalTheory.JSW.antiParts m d,
        MvPolynomial.C (GlobalTheory.JSW.jtDet m h l) * GlobalTheory.JSW.alternant A m (fun i => l i + GlobalTheory.JSW.staircase m i) := by
  exact @GlobalTheory.JSW.alternant_staircase_mul_antidiagonal
