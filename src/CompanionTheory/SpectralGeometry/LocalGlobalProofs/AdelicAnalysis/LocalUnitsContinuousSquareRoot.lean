module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem exists_sqrt_near_unit : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ,
    ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧
      (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  classical
  intro R _ _ hR x
  obtain ⟨htr, -, -, -, -, -, hval, U, -, hq⟩ := hR

  let h : R ≃ₜ R :=
    { toFun := fun y => y * (x : R)
      invFun := fun y => y * ((x⁻¹ : Rˣ) : R)
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  let f : U → R := fun u => (((u : Rˣ) ^ 2 : Rˣ) : R) * (x : R)
  have hf : IsOpenEmbedding f :=
    h.isOpenEmbedding.comp (hval.comp hq)
  have hf1 : f 1 = (x : R) := by simp [f]
  let a : R → Rˣ := fun y => if y ∈ Set.range f then ((Function.invFun f y : U) : Rˣ) else 1
  have haf : ∀ u : U, a (f u) = (u : Rˣ) := by
    intro u
    have : Function.invFun f (f u) = u := Function.leftInverse_invFun hf.injective u
    simp only [a, Set.mem_range_self, if_true, this]
  refine ⟨Set.range f, a, hf.isOpen_range, ⟨1, hf1⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hf.continuousAt_iff]
    have : a ∘ f = fun u : U => (u : Rˣ) := funext haf
    rw [this]
    exact continuous_subtype_val.continuousAt
  · intro y hy
    simp only [a, if_neg hy]
  · rintro _ ⟨u, rfl⟩
    rw [haf]
    simp [f]
  · have := haf 1
    rw [hf1] at this
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
