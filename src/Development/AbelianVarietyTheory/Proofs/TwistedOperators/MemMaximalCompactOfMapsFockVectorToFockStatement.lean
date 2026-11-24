module

public import Formalism.FormalDegreeBessel.StatementG
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemMaximalCompactOfMapsFockVectorToFock
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_maximalCompact_of_maps_fockVector_to_fock : ∀ (n : ℕ) (ε : Fin n → Bool) (fr G : Matrix (Fin n) (Fin n) ℂ) (σ Z : Type) [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (Z → ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (MvPolynomial σ ℂ)), IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → Function.Injective pt → R 1 = 1 → (∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, R (g * g') = R g * R g') → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ φ z, HasDerivAt (fun t : ℝ => R (NormedSpace.exp (t • X)) (pt φ) z) (pt (L X φ) z) 0) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R (fr⁻¹ * k * fr) (pt φ) = pt ψ) → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → (∃ j k, ε j ≠ ε k ∧ (fr * X * fr⁻¹) j k ≠ 0 ∧ (fr * X * fr⁻¹) k j ≠ 0) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ m : ℕ, (L X ^ m) φ ∈ F) → ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ φ φ', φ ≠ 0 → pt φ' = R g (pt φ) → ∃ k ∈ Formalism.REAL.Kset ε, g = fr⁻¹ * k * fr := by
  first | exact @GlobalTheory.Chain.RealIt.CompactStab.mem_compact | exact GlobalTheory.Chain.RealIt.CompactStab.mem_compact | (intros; apply GlobalTheory.Chain.RealIt.CompactStab.mem_compact <;> assumption)
