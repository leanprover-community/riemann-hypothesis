module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField

theorem l_theta : IntegralTraceSurjective := by
  intro E _ _ _ h
  obtain ⟨_, _, hun⟩ := h
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  let J : Ideal (𝓞 E) := Ideal.span {t | ∃ x, t = x + σ x}
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨θ, t, ht, hnot⟩ := hun P hP
    have htσ : t = σ θ := RingOfIntegers.ext (by rw [hσ]; exact ht)
    apply hnot
    have h1 : θ + σ θ ∈ P := hle (Ideal.subset_span ⟨θ, rfl⟩)
    have h2 : (1 : 𝓞 E) + σ 1 ∈ P := hle (Ideal.subset_span ⟨1, rfl⟩)
    rw [map_one] at h2
    have h3 : θ - t = (θ + σ θ) - (1 + 1) * σ θ := by rw [htσ]; ring
    rw [h3]
    exact P.sub_mem h1 (P.mul_mem_right _ h2)
  have key : ∀ y ∈ J, ∃ x, y * σ y = x + σ x := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, rfl⟩ := ht
      exact ⟨(x + σ x) * x, by simp only [map_add (f := _), map_mul, hσσ]; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ ih ih' =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨x', hx'⟩ := ih'
      exact ⟨x + x' + y * σ y', by simp only [map_add (f := _), map_mul, hσσ]; linear_combination hx + hx'⟩
    | smul a y _ ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨a * σ a * x, by simp only [smul_eq_mul, map_mul, hσσ]; linear_combination (a * σ a) * hx⟩
  obtain ⟨x, hx⟩ := key 1 (by rw [hJ]; exact Submodule.mem_top)
  refine ⟨x, ?_⟩
  rw [map_one, mul_one] at hx
  have h4 := congrArg (fun z : 𝓞 E => (z : E)) hx
  simp only [map_add (f := _), map_one] at h4
  rw [← hσ]
  exact h4.symm

end Formalism.MainNotions.BridgeLemma

end
