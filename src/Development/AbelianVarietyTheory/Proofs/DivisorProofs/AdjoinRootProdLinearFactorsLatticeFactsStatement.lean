module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFacts
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

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  first | exact @GlobalTheory.herbrand_lattice_facts | exact GlobalTheory.herbrand_lattice_facts | (intros; apply GlobalTheory.herbrand_lattice_facts <;> assumption)
