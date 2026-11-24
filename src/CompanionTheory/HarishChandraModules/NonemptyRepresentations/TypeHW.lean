module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
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
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.StatementQr
import Formalism.RealPlaceAnalysis.StatementA
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.TypeHW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem prod_Icc (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => f (j + 1)) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

end CompanionTheory.D.Inhab.TypeHW
