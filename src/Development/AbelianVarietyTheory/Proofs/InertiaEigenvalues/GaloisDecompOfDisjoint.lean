module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
namespace GlobalTheory.InertiaEigenvalues

theorem galois_decomp_of_disjoint : ∀ (l : ℕ) [Fact l.Prime] (K M : IntermediateField ℚ_[l] (Om l)), FiniteDimensional ℚ_[l] K → IsGalois ℚ_[l] K → K ⊓ M = ⊥ → ∀ g : GQ l, ∃ h ∈ K.fixingSubgroup, ∃ k ∈ M.fixingSubgroup, g = h * k := by
  intro l _ K M _ _ hKM g
  let r : GQ l →* (K ≃ₐ[ℚ_[l]] K) := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) K
  have hr : ∀ (σ : GQ l) (y : K), ((r σ y : K) : Om l) = σ (y : Om l) := fun σ y =>
    AlgEquiv.restrictNormal_commutes σ K y
  let H : Subgroup (K ≃ₐ[ℚ_[l]] K) := M.fixingSubgroup.map r
  have hfix : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxM : (x : Om l) ∈ M := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup M]
      intro k
      have := hx ⟨r k, Subgroup.mem_map_of_mem r k.2⟩
      have h2 := congrArg (fun z : K => (z : Om l)) this
      change (k : GQ l) (x : Om l) = x
      simpa [hr] using h2
    have hxKM : (x : Om l) ∈ K ⊓ M := ⟨x.2, hxM⟩
    rw [hKM, IntermediateField.mem_bot] at hxKM
    obtain ⟨c, hc⟩ := hxKM
    rw [IntermediateField.mem_bot]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa using hc
  have hH : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hfix, IntermediateField.fixingSubgroup_bot]
  have hg : r g ∈ H := by rw [hH]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
  refine ⟨g * k⁻¹, ?_, k, hk, by group⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 : r (g * k⁻¹) = 1 := by rw [map_mul, map_inv, ← hkg, mul_inv_cancel]
  have := hr (g * k⁻¹) ⟨x, hx⟩
  rw [h1] at this
  simpa using this.symm

end GlobalTheory.InertiaEigenvalues
