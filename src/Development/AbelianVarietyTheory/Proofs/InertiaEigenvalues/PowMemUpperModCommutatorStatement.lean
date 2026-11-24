module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutator
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

theorem _root_.GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | exact GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator <;> assumption)
