module

public import Mathlib.RingTheory.Smooth.Basic
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

open KaehlerDifferential
namespace GlobalTheory
theorem bertini_derivation_split : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  intro k A _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A (KaehlerDifferential k A)
  refine ⟨n, fun l => (LinearMap.proj l ∘ₗ g).compDer (KaehlerDifferential.D k A), fun l => f (Pi.single l 1), ?_⟩
  intro a
  have h := LinearMap.congr_fun hfg (KaehlerDifferential.D k A a)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_lhs => rw [← h]
  conv_lhs => rw [pi_eq_sum_univ (g (KaehlerDifferential.D k A a))]

  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]
end GlobalTheory
