module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bracket
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.glRel :
    ∀ (n : ℕ) (Ξ : Pre n), Formalism.REAL.GlRel Ξ.E := by
  intro n Ξ a b c d
  have h := UpperTheory.V.Weyl.bracket n Ξ a b (Matrix.single c d 1)
  have h1 : Ξ.D (Matrix.single a b (1:ℂ) * Matrix.single c d 1) = if b = c then Ξ.E a d else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  have h2 : Ξ.D (Matrix.single c d (1:ℂ) * Matrix.single a b 1) = if d = a then Ξ.E c b else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  rw [map_sub, h1, h2] at h
  exact h
