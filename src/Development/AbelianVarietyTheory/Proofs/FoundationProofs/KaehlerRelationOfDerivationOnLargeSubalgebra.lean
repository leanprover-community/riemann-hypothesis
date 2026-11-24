module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.AlmostEt

open Finsupp

theorem kerTotal_gen_local {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (g : S →₀ S)
    (hg : g ∈ ((Set.range fun x : S × S => single x.1 1 + single x.2 1 - single (x.1 + x.2) 1) ∪
        Set.range fun x : S × S => single x.2 x.1 + single x.1 x.2 - single (x.1 * x.2) 1) ∪
      Set.range fun x : A => single (algebraMap A S x) 1) :
    ∃ F : Finset S, ∀ C : Subalgebra A S, (↑F : Set S) ⊆ C →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        Finsupp.linearCombination S D g = 0 := by
  classical
  rcases hg with (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩) | ⟨a, rfl⟩
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.add u hu w hw]
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.mul u hu w hw, add_comm]
  · refine ⟨∅, fun C _ M _ _ D hD => ?_⟩
    simp [hD.alg a]

theorem kaehler_rel_local : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ)
    (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 →
    ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        ∑ i, x i • D (y i) = 0 := by
  intro A S _ _ _ n x y h
  classical
  set v : S →₀ S := ∑ i, single (y i) (x i) with hv
  have hlc : ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M),
      Finsupp.linearCombination S D v = ∑ i, x i • D (y i) := by
    intro M _ _ D

    simp [hv, map_sum, Finsupp.linearCombination_single]
  have hmem : v ∈ KaehlerDifferential.kerTotal A S := by
    rw [← KaehlerDifferential.kerTotal_eq, LinearMap.mem_ker, hlc, h]
  obtain ⟨G, hGs, hvG⟩ := Submodule.mem_span_finite_of_mem_span hmem
  have key := fun g (hg : g ∈ G) => kerTotal_gen_local (A := A) g (hGs hg)
  choose F hF using key
  refine ⟨G.attach.biUnion (fun g => F g.1 g.2), ?_⟩
  intro C hC _ M _ _ D hD
  rw [← hlc]
  have hle : Submodule.span S (↑G : Set (S →₀ S)) ≤
      LinearMap.ker (Finsupp.linearCombination S D) := by
    rw [Submodule.span_le]
    intro g hg
    refine hF g hg C (fun z hz => hC ?_) M D hD
    simp only [Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion]
    exact ⟨⟨g, hg⟩, hz⟩
  exact hle hvG

end GlobalTheory.AlmostEt
