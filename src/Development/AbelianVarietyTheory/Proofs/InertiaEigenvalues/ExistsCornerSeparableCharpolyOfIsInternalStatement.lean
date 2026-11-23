module

public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternal
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal : ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_corner_separable_charpoly | exact GlobalTheory.SpanRing.exists_corner_separable_charpoly | (intros; apply GlobalTheory.SpanRing.exists_corner_separable_charpoly <;> assumption)
