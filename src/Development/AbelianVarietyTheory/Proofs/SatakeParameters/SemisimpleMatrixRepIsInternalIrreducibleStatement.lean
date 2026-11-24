module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)), DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  first | exact @GlobalTheory.semisimple_matrix_rep_decomp | exact GlobalTheory.semisimple_matrix_rep_decomp | (intros; apply GlobalTheory.semisimple_matrix_rep_decomp <;> assumption)
