module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.slashIntMatrixPosDet_properties : ∀ (k : ℕ) (f : ℍ → ℂ), 1 ≤ k → (∀ δ δ' : M2, 0 < δ.det → 0 < δ'.det → slz k (δ * δ') f = slz k δ' (slz k δ f)) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ)) ∧ (∀ (L : ℕ) (χ : ℤ → ℂ), Inv k L χ f ↔ ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → slz k (γ : M2) f = fun τ => χ (γ 1 1) * f τ) ∧ (∀ δ : M2, 0 < δ.det → Continuous f → Continuous (slz k δ f)) ∧ ∀ (n : ℕ) (τ : ℍ), 0 < n → slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  first | exact @GlobalTheory.EisM.slz_props | exact GlobalTheory.EisM.slz_props | (intros; apply GlobalTheory.EisM.slz_props <;> assumption)
