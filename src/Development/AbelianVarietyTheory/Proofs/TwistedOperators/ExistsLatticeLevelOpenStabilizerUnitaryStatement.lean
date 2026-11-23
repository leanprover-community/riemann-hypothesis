module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeLevelOpenStabilizerUnitary
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_lattice_level_open_stabilizer_unitary : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  first | exact @GlobalTheory.WeilLevelStab.exists_level_stab | exact GlobalTheory.WeilLevelStab.exists_level_stab | (intros; apply GlobalTheory.WeilLevelStab.exists_level_stab <;> assumption)
