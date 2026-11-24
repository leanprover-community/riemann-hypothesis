module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernel
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.gaussian_inner_eq_invariantKernel : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  first | exact @GlobalTheory.OscGauss.kerAlg | exact GlobalTheory.OscGauss.kerAlg | (intros; apply GlobalTheory.OscGauss.kerAlg <;> assumption)
