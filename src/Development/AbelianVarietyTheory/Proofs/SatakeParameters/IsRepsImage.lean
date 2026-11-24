module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
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

@[expose] public section

namespace GlobalTheory.RepresentativesImage

theorem isReps_image {V W : Type} [AddCommGroup V] [AddCommGroup W] [DecidableEq W] (T : V ≃+ W)
    {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S) (h₁ : ∀ x : V, T x ∈ M₁ ↔ x ∈ Λ₁) (h₂ : ∀ x : V, T x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → W) S) := by
  unfold Formalism.L2.Th1.H.IsReps at hS ⊢
  obtain ⟨hmem, hdist, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact (h₂ v).2 (hmem v hv)
  · intro a ha b hb hab
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
    rw [← map_sub] at hab
    rw [hdist v hv u hu ((h₁ _).1 hab)]
  · intro w hw
    obtain ⟨v, rfl⟩ := T.surjective w
    obtain ⟨u, hu, hvu⟩ := hcov v ((h₂ v).1 hw)
    exact ⟨T u, Finset.mem_image_of_mem _ hu, by rw [← map_sub]; exact (h₁ _).2 hvu⟩

end GlobalTheory.RepresentativesImage
