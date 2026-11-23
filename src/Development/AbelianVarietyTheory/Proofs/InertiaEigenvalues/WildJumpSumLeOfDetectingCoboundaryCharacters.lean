module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfCoboundaryDetectsStatement
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

namespace GlobalTheory.PMon.Ram

theorem jumpSum_le_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hax hdet
  obtain ⟨j, hinj, hrange, happ, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A

  have haxF : AxIn (IntermediateField.fixedField A) L p := by
    intro J x hx
    obtain ⟨y, hy, hxy⟩ := hax (J.map j) x (by
      rintro σ ⟨τ, hτ, rfl⟩
      rw [happ]
      exact hx τ hτ)
    refine ⟨y, fun τ hτ => ?_, hxy⟩
    rw [← happ]
    exact hy (j τ) ⟨τ, hτ, rfl⟩
  have hdetF : Detects p r ⊤ (B.comap j) := by
    intro τ₀ _ hτ₀
    have hA : j τ₀ ∈ A := hrange.le (MonoidHom.mem_range.mpr ⟨τ₀, rfl⟩)
    obtain ⟨x, a, hxa, hnd⟩ := hdet (j τ₀) hA hτ₀
    refine ⟨x, fun τ => a (j τ), fun τ _ => ?_, hnd⟩
    obtain ⟨z, hz, hzx⟩ := hxa (j τ) (hrange.le (MonoidHom.mem_range.mpr ⟨τ, rfl⟩))
    refine ⟨z, hz, ?_⟩
    rw [← happ]
    exact hzx
  have key := GlobalTheory.T.wild_jumpSum_le_of_coboundary_detects (IntermediateField.fixedField A) L p E r (B.comap j) hp hE hord haxF hdetF
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  rw [hwild, jumpSum_comap_injective _ _ j _ B hinj, hrange] at key
  exact key

end GlobalTheory.PMon.Ram
