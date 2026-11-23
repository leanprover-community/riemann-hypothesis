module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory

theorem isFibreFamily_map_homeomorph : ∀ (V V' X X' : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] (e : V ≃ₜ V') (r : X ≃ₜ X') (μ : Measure V) (ν : Measure X) (f : V → X) (f' : V' → X') (B : Set X) (fib : X → Measure V), (∀ v, f' (e v) = r (f v)) → IsFibreFamily μ f id Set.univ ν B fib → IsFibreFamily (μ.map e) f' id Set.univ (ν.map r) (r '' B) fun b => (fib (r.symm b)).map e := by
  intro V V' X X' _ _ _ _ _ _ _ _ _ _ _ _ e r μ ν f f' B fib hf h
  obtain ⟨h1, h2, h3⟩ := h
  have he : MeasurableEmbedding e := e.measurableEmbedding
  have hr : MeasurableEmbedding r := r.measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [he.map_apply]
    convert h1 (r.symm b) using 2
    ext v
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.inter_univ, Set.mem_singleton_iff, id, hf]
    exact not_congr r.eq_symm_apply.symm
  · have := h2 (fun v => φ (e v)) (hφ.comp he.measurable)
    rw [Measure.restrict_univ] at this ⊢
    rw [he.lintegral_map, hr.lintegral_map, this]
    refine lintegral_congr fun b => ?_
    rw [he.lintegral_map, r.symm_apply_apply]
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [he.integrable_map_iff, r.symm_apply_apply]
      exact h4 b hb
    · have h6 := h5.comp (s := r '' B) r.symm.continuous.continuousOn (by
        rintro _ ⟨b, hb, rfl⟩
        rw [r.symm_apply_apply]
        exact hb)
      refine h6.congr fun b _ => ?_
      simp only [Function.comp]
      rw [he.integral_map]

end GlobalTheory
