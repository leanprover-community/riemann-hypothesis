module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupAbelianNatStatement
import GroundTheory.LocalFields.ConductorReciprocity
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  intro F _ _ _ _ M _ _ p e v hv hOrd σ hσ

  have hc : (0 : ℤ) ≤ ⌈v⌉ := Int.ceil_nonneg hv
  have hn : ((⌈v⌉.toNat : ℕ) : ℝ) = ((⌈v⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc
  have hσn : σ ∈ upperRamificationGroup F ↥M ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn, ← upperRamificationGroup_eq_ceil]
    exact hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' F M p e ⌈v⌉.toNat hOrd σ hσn

  have hvn : v ≤ ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn]; exact Int.le_ceil v
  have hle : min (2 * v) (v + e) ≤ ((min (2 * ⌈v⌉.toNat) (⌈v⌉.toNat + e) : ℕ) : ℝ) := by
    push_cast
    exact min_le_min (by linarith) (by linarith)
  exact upperRamificationGroup_antitone F ↥M hle hpow

end GlobalTheory.PMon.Ram
