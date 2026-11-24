module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Projectivization.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]

instance : TopologicalSpace (ℙ K V) :=
  TopologicalSpace.coinduced (Projectivization.mk' K) inferInstance

namespace ProjTopology

lemma continuous_mk' : Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_coinduced_rng

lemma isOpen_iff {s : Set (ℙ K V)} :
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) :=
  isOpen_coinduced

lemma continuous_iff {Y : Type*} [TopologicalSpace Y] {g : ℙ K V → Y} :
    Continuous g ↔ Continuous (g ∘ Projectivization.mk' K) :=
  continuous_coinduced_dom

end ProjTopology

instance compactSpace_projectivization_complex (N : ℕ) : CompactSpace (ℙ ℂ (Fin (N + 1) → ℂ)) := by
  have hS : IsCompact (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_sphere 0 1
  have : CompactSpace (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_iff_compactSpace.mp hS
  have hne : ∀ w : Metric.sphere (0 : Fin (N + 1) → ℂ) 1, (w : Fin (N + 1) → ℂ) ≠ 0 := by
    intro w h
    have := w.2
    rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this
    exact zero_ne_one this
  let g : Metric.sphere (0 : Fin (N + 1) → ℂ) 1 → ℙ ℂ (Fin (N + 1) → ℂ) := fun w =>
    Projectivization.mk' ℂ ⟨w.1, hne w⟩
  have hg : Continuous g :=
    ProjTopology.continuous_mk'.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hsurj : Function.Surjective g := by
    intro v
    induction v using Projectivization.ind with
    | h w hw =>
      have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      refine ⟨⟨(‖w‖⁻¹ : ℂ) • w, ?_⟩, ?_⟩
      · rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ hn]
      · change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ w hw
        rw [Projectivization.mk_eq_mk_iff]
        exact ⟨Units.mk0 (‖w‖⁻¹ : ℂ) (inv_ne_zero (by exact_mod_cast hn)), rfl⟩
  refine ⟨?_⟩
  rw [← hsurj.range_eq]
  exact isCompact_range hg

end GroundTheory.Heights₂.Heights
