module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixRangeEq
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.CapelliCentralEnveloping
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Formalism.PieriBlockIdeals.Statement

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem exists_square_matrix_of_submodule_between
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | (apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq ..)
