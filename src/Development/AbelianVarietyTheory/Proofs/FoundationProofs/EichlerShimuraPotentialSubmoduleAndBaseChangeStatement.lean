module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraPotentialSubmoduleAndBaseChange
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.eichlerShimuraPotential_submodule_and_base_change : ∀ (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)), (∀ F G, F ∈ Pot R w Γ → G ∈ Pot R w Γ → F + G ∈ Pot R w Γ) ∧ (0 ∈ Pot R w Γ) ∧ (∀ (c : R) F, F ∈ Pot R w Γ → c • F ∈ Pot R w Γ) ∧ (∀ F G, F ∈ Triv R w Γ → G ∈ Triv R w Γ → F + G ∈ Triv R w Γ) ∧ (∀ (c : R) F, F ∈ Triv R w Γ → c • F ∈ Triv R w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Pot R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Pot S w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Triv R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Triv S w Γ) := by
  first | exact @GlobalTheory.KZ.pot_triv_lin | exact GlobalTheory.KZ.pot_triv_lin | (intros; apply GlobalTheory.KZ.pot_triv_lin <;> assumption)
