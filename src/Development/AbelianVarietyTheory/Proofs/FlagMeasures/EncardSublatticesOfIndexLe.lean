module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Formalism.HermitianLattices.StatementMass
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem sublattice_count : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ M hM i hi
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.IsTorsionFree (𝓞 K) M := inferInstance
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
    have h1 : Module.rank (𝓞 K) M ≤ Module.rank K V := by
      rw [IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
      exact Submodule.rank_le M
    exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K V)
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (Module.finrank K V) i hi hr
  have hinj : Set.InjOn (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i} := by
    intro N hN N' hN' e
    have := congrArg (Submodule.map M.subtype) e
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr hN.1, inf_eq_right.mpr hN'.1] using this
  have hmaps : Set.MapsTo (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}
      {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i} := by
    intro N hN
    exact hN.2
  have h2 := Set.encard_le_encard_of_injOn hmaps hinj
  rw [← hfin.cast_ncard_eq] at h2
  calc _ ≤ (((({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast h2
    _ = ENNReal.ofReal ({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℝ) := by
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

end GlobalTheory.Mass
