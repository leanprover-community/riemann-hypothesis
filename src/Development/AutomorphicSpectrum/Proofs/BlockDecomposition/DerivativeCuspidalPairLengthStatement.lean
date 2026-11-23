module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.derivative_cuspidal_pair_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {p q N c : ℕ} (u v : IrrGL (k := k)) (s : Fin p → IrrGL (k := k)) (t : Fin q → IrrGL (k := k)) (hs : ∑ i, (s i).1 = u.1) (ht : ∑ i, (t i).1 = v.1) (d : ℕ) (hsd : ∀ i, (s i).1 = d) (htd : ∀ j, (t j).1 = d) (hsc : ∀ i, (s i).IsCusp) (htc : ∀ i, (t i).IsCusp) (hu : Nonempty ((jac (stdBlocks (fun i => (s i).1) hs) u.rep).Equiv (piTensor fun i => (s i).rep))) (hv : Nonempty ((jac (stdBlocks (fun i => (t i).1) ht) v.rep).Equiv (piTensor fun i => (t i).rep))) (hd : ∑ i, (![u, v] i).1 = N) (y : Fin c → IrrGL (k := k)) (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy (prodIrr ![u, v] hd)), ∃ (f : Fin p ↪o Fin c) (g : Fin q ↪o Fin c), Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = s i) ∧ ∀ j, y (g j) = t j := by
  first | exact @GlobalTheory.CompanionTheory.Shuffle2.shuffle2 | exact GlobalTheory.CompanionTheory.Shuffle2.shuffle2 | (intros; apply GlobalTheory.CompanionTheory.Shuffle2.shuffle2 <;> assumption)
