module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.outerTensor_fockOnePlace_iso_unitaryFock : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ), Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  first | exact @GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | exact GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | (intros; apply GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso <;> assumption)
