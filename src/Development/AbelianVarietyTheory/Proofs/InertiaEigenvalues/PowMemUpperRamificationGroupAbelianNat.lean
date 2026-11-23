module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMinStatement
public import GroundTheory.LocalFields.ConductorReciprocity
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_abelian_nat :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ),
      OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ),
        σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  intro F _ _ _ _ M _ _ p e n h σ hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M n] at hσ
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M
    (min (2 * n) (n + e)), ← map_pow]
  exact Subgroup.mem_map_of_mem _ (GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min F p e n h x hx)

end GlobalTheory.PMon.Ram
