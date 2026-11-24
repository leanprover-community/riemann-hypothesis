module

public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBound
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.admissible_off_type_family_bound : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.LevelBudget.admissible_off_type_level_budget | exact GlobalTheory.LevelBudget.admissible_off_type_level_budget | (intros; apply GlobalTheory.LevelBudget.admissible_off_type_level_budget <;> assumption)
