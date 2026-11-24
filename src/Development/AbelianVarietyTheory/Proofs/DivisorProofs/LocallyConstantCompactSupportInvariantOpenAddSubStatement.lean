module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantCompactSupportInvariantOpenAddSub
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

@[expose] public section


theorem _root_.GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g → ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  first | exact @GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | exact GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | (intros; apply GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup <;> assumption)
