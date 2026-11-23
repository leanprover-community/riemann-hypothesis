module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.exists_of_pow_le_of_pow_le :
    ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι)
      (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I →
      ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  intro S A _ _ s I ι TB I' n m _ _ _ h1 h2
  have hk : ∀ k : ℕ, I ^ (n * k) ≤ I' ^ k := fun k => by
    rw [pow_mul]; exact Ideal.pow_right_mono h1 k
  classical
  refine ⟨{ TB with fin := ?_, approx := ?_, complete := ?_ }, rfl, rfl⟩
  · intro x k
    exact (TB.fin x (n * k)).subset fun i hi h => hi (hk k h)
  · intro x k F hF
    set G : Finset ι := F ∪ (TB.fin x (n * k)).toFinset with hG
    have hG' : ∀ i, i ∉ G → TB.c i x ∈ I ^ (n * k) := by
      intro i hi
      by_contra h
      exact hi (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hmain := TB.approx x (n * k) G hG'
    have hmap : (I ^ (n * k)).map s ≤ (I' ^ k).map s := Ideal.map_mono (hk k)
    have hsplit : ∑ i ∈ G, s (TB.c i x) * TB.b i =
        ∑ i ∈ F, s (TB.c i x) * TB.b i + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_union_left)]
    have hrest : ∑ i ∈ G \ F, s (TB.c i x) * TB.b i ∈ (I' ^ k).map s := by
      refine Ideal.sum_mem _ fun i hi => ?_
      have : i ∉ F := (Finset.mem_sdiff.1 hi).2
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i this))
    have : x - ∑ i ∈ F, s (TB.c i x) * TB.b i =
        (x - ∑ i ∈ G, s (TB.c i x) * TB.b i) + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [hsplit]; ring
    rw [this]
    exact add_mem (hmap hmain) hrest
  · refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le A (I.map s) (I'.map s) n m ?_ ?_ TB.complete
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h1
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h2

end GlobalTheory.BSP
