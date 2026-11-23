module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasis
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

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F), (∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) → f = g := by
  first | exact @GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | exact GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | (intros; apply GlobalTheory.continuousMultilinearMap_ext_hilbertBasis <;> assumption)
