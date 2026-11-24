module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

theorem _root_.GlobalTheory.T.reducible_cuspidal_pair_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  first | exact @GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | exact GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | (intros; apply GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient <;> assumption)
