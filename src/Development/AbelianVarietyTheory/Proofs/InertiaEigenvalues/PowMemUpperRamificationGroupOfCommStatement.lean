module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupOfComm
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_of_comm' : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm <;> assumption)
