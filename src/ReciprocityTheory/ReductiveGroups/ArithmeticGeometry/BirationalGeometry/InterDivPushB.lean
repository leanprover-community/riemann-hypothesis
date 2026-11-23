module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_divSupp_of_eval {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (h0 : eval z (map (Int.castRingHom ℂ) s) = 0) :
    ∃ W' ∈ divSupp P s, IsHorizontal W' ∧ z ∈ mcPts W' := by
  classical
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun f => rfl
  haveI hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    rw [sup_le_iff, Ideal.span_le, Set.singleton_subset_iff]
    refine ⟨fun f hf => ?_, ?_⟩
    · rw [RingHom.mem_ker, hφ]
      exact hz.2 f hf
    · show s ∈ RingHom.ker φ
      rw [RingHom.mem_ker, hφ]
      exact h0
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hmem : ∀ f ∈ W', eval z (map (Int.castRingHom ℂ) f) = 0 := fun f hf => by
    have := hW'le hf
    rwa [RingHom.mem_ker, hφ] at this
  refine ⟨W', ⟨hW', ?_⟩, ?_, ⟨hz.1, hmem⟩⟩
  · intro k
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun hX => hi (by simpa using hmem _ hX)⟩
  · show Ideal.comap _ W' = ⊥
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap] at hn
    rw [Ideal.mem_bot]
    have := hmem _ hn
    simpa using this

end ReciprocityTheory.ChartRestriction.G.Geo
