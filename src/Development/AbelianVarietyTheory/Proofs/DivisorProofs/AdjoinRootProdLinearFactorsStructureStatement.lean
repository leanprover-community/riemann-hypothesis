module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsStructure
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.adjoinRootProdLinearFactors_structure : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S] (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧ lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧ (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧ (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧ (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  first | exact @GlobalTheory.RingFacts.ring_facts | exact GlobalTheory.RingFacts.ring_facts | (intros; apply GlobalTheory.RingFacts.ring_facts <;> assumption)
