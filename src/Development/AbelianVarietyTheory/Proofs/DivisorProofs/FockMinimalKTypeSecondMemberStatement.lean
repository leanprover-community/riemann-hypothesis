module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
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

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_minimal_KType_second_member : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  first | exact @GlobalTheory.FockAlg.min_second | exact GlobalTheory.FockAlg.min_second | (intros; apply GlobalTheory.FockAlg.min_second <;> assumption)
