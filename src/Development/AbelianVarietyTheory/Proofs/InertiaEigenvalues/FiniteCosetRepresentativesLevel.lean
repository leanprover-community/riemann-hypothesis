module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerRightBlockMulBlockTriangular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section
namespace GlobalTheory.LevReps

theorem reps : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ F : Finset (Bridge.Gf S), (∀ u ∈ F, u ∈ B.levJ ψ) ∧
      ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  first
  | exact @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | (apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ ..)

end GlobalTheory.LevReps
end
