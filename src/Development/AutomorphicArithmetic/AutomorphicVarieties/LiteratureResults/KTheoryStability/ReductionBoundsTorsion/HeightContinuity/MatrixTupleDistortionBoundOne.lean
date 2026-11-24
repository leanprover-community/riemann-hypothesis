module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Diagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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

@[expose] public section

open Matrix

noncomputable section

namespace PositivityTheory.KB.HeightDistance

def nsq {N : ℕ} (v : Fin N → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def dist1 {ι : Type} [Fintype ι] {N : ℕ} (A : ι → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 + ∑ w, ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) ^ 2

theorem nsq_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun i _ => by positivity

theorem one_le_dist1 {ι : Type} [Fintype ι] {N : ℕ} (A : ι → Matrix (Fin N) (Fin N) ℂ) :
    1 ≤ dist1 A := by
  unfold dist1
  have h0 : 0 ≤ ∑ w, ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ :=
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  nlinarith

end PositivityTheory.KB.HeightDistance
