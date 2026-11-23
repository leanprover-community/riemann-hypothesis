module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariable
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

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cmLattice_heisenberg_relations_one_variable : ∀ d : ℕ, 0 < d → (∀ (x y : ℂ) (F : ℂ → ℂ), U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) * U1 d (x + y) F z) ∧ (∀ F, U1 d 0 F = F) ∧ (∀ (x : ℂ) (F : ℂ → ℂ), Differentiable ℂ F → Differentiable ℂ (U1 d x F) ∧ Differentiable ℂ (W1 d x F)) ∧ (∀ (x : ℂ) (F : ℂ → ℂ) (z : ℂ), U1 d x (fun z => F (-z)) z = U1 d (-x) F (-z)) ∧ (∀ (x y : ℂ) (F : ℂ → ℂ), d % 4 = 3 → InOK d (x * conj y) → W1 d x (W1 d y F) = W1 d (x + y) F) ∧ (∀ (θ : ℂ → ℂ) (t l z : ℂ), W1 d l θ = θ → U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l))) ∧ (∀ (x : ℂ) (f F : ℂ → ℂ) (z : ℂ), W1 d x (fun z => f z * F z) z = f (z + x) * W1 d x F z ∧ U1 d x (fun z => f z * F z) z = f (z + x) * U1 d x F z) ∧ ∀ (x y z : ℂ), kap1 d x (y + z) = kap1 d x y * kap1 d x z ∧ kap1 d (x + y) z = kap1 d x z * kap1 d y z := by
  first | exact @GlobalTheory.MomOne.heisenbergOne | exact GlobalTheory.MomOne.heisenbergOne | (intros; apply GlobalTheory.MomOne.heisenbergOne <;> assumption)
