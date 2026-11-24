module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FdegHCRowsMulSuperfactorialLeVandermonde
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

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.fdegHC_rows_mul_superfactorial_le_vandermonde : ∀ (R : Ranks) (P Q : HCParam R), Q.v = P.v → Q.b = P.b → ∀ B : ℝ, 1 ≤ B → (∀ i j, ((P.v i : ℚ) : ℝ) + ((P.b j : ℚ) : ℝ) ≤ B) → (∀ j j', ((P.b j' : ℚ) : ℝ) - ((P.b j : ℚ) : ℝ) ≤ B) → Formalism.QuantumDeterminants.fdegHC (Formalism.MainNotions.S.lamSH R P) * Formalism.MainNotions.StandardLattice.facProd R.r ≤ B ^ ((R.k - 1) * R.m + R.m * (R.m - 1) / 2) * Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) := by
  first | exact @GlobalTheory.FdegRowsBound.fdeg_rows_le | exact GlobalTheory.FdegRowsBound.fdeg_rows_le | (intros; apply GlobalTheory.FdegRowsBound.fdeg_rows_le <;> assumption)
